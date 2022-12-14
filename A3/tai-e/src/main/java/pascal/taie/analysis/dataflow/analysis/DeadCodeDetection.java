/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me

        //控制流不可达代码
        Stack<Stmt> bfs = new Stack<>();
        Set<Stmt> accessible = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        bfs.add(cfg.getEntry());
        while(!bfs.empty()){
            Stmt st = bfs.pop();
            if(!accessible.contains(st)){
                accessible.add(st);
                for(Stmt node : cfg.getSuccsOf(st)){
                    bfs.add(node);
                }
            }
        }
        for(Stmt node:cfg){
            if(!accessible.contains(node)){
                deadCode.add(node);
            }
        }

        accessible.clear();
        bfs.clear();
        Set<Stmt> defendloop = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        for(Stmt node:cfg) {
            if (node instanceof AssignStmt) {//无用赋值
//                Var left = ((AssignStmt<Var, RValue>) node).getLValue(); 不一定是变量可能是字段存储
                LValue left = ((AssignStmt<LValue, RValue>) node).getLValue();
                RValue right = ((AssignStmt<LValue, RValue>) node).getRValue();
                if (left instanceof Var && !liveVars.getOutFact(node).contains((Var) left) && hasNoSideEffect(right)) {
                    deadCode.add(node);//右边无副作用，左边不是活跃变量
                }
            }
        }

        bfs.add(cfg.getEntry());
        while(!bfs.empty()){
            Stmt node = bfs.pop();
            defendloop.add(node);
            if(!accessible.contains(node)) {
                accessible.add(node);
            }
            if(node instanceof If){//分支不可达代码
                Value condition = ConstantPropagation.evaluate(((If) node).getCondition(),constants.getInFact(node));
                if(condition.isConstant()){
                    int con = condition.getConstant();
                    if(con==0){
                        cfg.getOutEdgesOf(node).forEach(out->{
                            if(out.getKind()== Edge.Kind.IF_FALSE){
                                bfs.add(out.getTarget());
                            }
                        });
                    }
                    else{
                        Stmt tar = ((If) node).getTarget();
                        if(!defendloop.contains(tar)){
                            defendloop.add(tar);
                            bfs.add(tar);
                        }
                    }
                }
                else{
                    for(Stmt temp:cfg.getSuccsOf(node)){
                        bfs.add(temp);
                    }
                }
            }
            else if(node instanceof SwitchStmt){//分支不可达代码
                Value condition = ConstantPropagation.evaluate(((SwitchStmt) node).getVar(),constants.getInFact(node));
                if(condition.isConstant()){
                    AtomicBoolean defaultchoose = new AtomicBoolean(true);
                    int con = condition.getConstant();
                    cfg.getOutEdgesOf(node).forEach(out->{
                        if(out.isSwitchCase()&&con==out.getCaseValue()){
                            bfs.add(out.getTarget());
                            defaultchoose.set(false);
                        }
                    });
                    if(defaultchoose.get()){
                        bfs.add(((SwitchStmt) node).getDefaultTarget());
                    }
                }
                else{
                    for(Stmt temp:cfg.getSuccsOf(node)){
                        bfs.add(temp);
                    }
                }
            }
            else{
                for(Stmt temp:cfg.getSuccsOf(node)){
                    if(!defendloop.contains(temp)){
                        bfs.add(temp);
                    }
                }
            }
        }
        for(Stmt node:cfg){
            if(!accessible.contains(node)){
                deadCode.add(node);
            }
        }
        if(deadCode.contains(cfg.getExit())){ //原来那个[13@L-1]nop是exit
            deadCode.remove(cfg.getExit());
        }
        if(deadCode.contains(cfg.getEntry())){
            deadCode.remove(cfg.getEntry());
        }
        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
