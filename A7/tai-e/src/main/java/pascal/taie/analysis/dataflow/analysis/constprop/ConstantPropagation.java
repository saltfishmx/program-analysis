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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;
import java.util.Set;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact fact = new CPFact();
        IR ir = cfg.getIR();
        for(Var v : ir.getParams()){
            if( canHoldInt(v)){
                fact.update(v,Value.getNAC());
            }
        }
//需要注意的是：在实现 newBoundaryFact() 的时候，你要小心地处理每个会被分析的方法的参数。具体来说，你要将它们的值初始化为 NAC
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        CPFact fact = new CPFact();
        return fact;
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.forEach((k,v)->{
            Value tv = target.get(k);
            Value newvalue = meetValue(v,tv);
            target.update(k,newvalue);
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if(v1.isNAC()||v2.isNAC()){
            return Value.getNAC();
        }
        else if(v1.isUndef()&&v2.isUndef()){
            return Value.getUndef();
        }
        else if(v1.isUndef()&&v2.isConstant()){
            return v2;
        }
        else if(v1.isConstant()&&v2.isUndef()){
            return v1;
        }
        else{
            if(v1.getConstant()==v2.getConstant()){
                return v1;
            }
            else{
                return Value.getNAC();
            }
        }
        //return null;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if(stmt.getDef().isPresent() && stmt.getDef().get().getClass()==Var.class)//你只需要关注等号左侧为变量且右侧只能是如下几类表达式的赋值语句：
        {
            DefinitionStmt defStmt=(DefinitionStmt) stmt;
            Var def= (Var) defStmt.getDef().get();
            if (canHoldInt(def)){
                Value gen = evaluate(defStmt.getRValue(), in);
                boolean flag=in.update(def,gen);
                return out.copyFrom(in);
            }
            else
                return out.copyFrom(in);
        }
        else
            return out.copyFrom(in);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me

        if(exp instanceof IntLiteral){//x=c
            int v = ((IntLiteral) exp).getValue();
            Value res = Value.makeConstant(v);
            return res;
        }
        else if(exp instanceof Var && canHoldInt((Var) exp)){//x=y
            Value vl = in.get((Var) exp);
            if(!vl.isConstant()){
                if(vl.isNAC()){
                    return Value.getNAC();
                }
                if(vl.isUndef()){
                    return Value.getUndef();
                }
            }
            int v = vl.getConstant();
            Value res = Value.makeConstant(v);
            return res;

        }
        else if(exp instanceof BinaryExp &&canHoldInt(((BinaryExp) exp).getOperand1())&&canHoldInt(((BinaryExp) exp).getOperand2())){
            //x = y op z
            Var op1 = ((BinaryExp) exp).getOperand1();
            Var op2 = ((BinaryExp) exp).getOperand2();
            Value v1 = in.get(op1);
            Value v2 = in.get(op2);
            if(v1.isNAC()&&v2.isConstant()){
                if(exp instanceof ArithmeticExp){
                    if ((((ArithmeticExp) exp).getOperator()== ArithmeticExp.Op.DIV||((ArithmeticExp) exp).getOperator()== ArithmeticExp.Op.REM) && v2.getConstant()==0){
                        return Value.getUndef();
                    }
                }
            }
            if(v1.isNAC()||v2.isNAC()){
                return Value.getNAC();
            }
            else if(v1.isConstant()&&v2.isConstant()){
                int a = v1.getConstant();
                int b = v2.getConstant();
                int v=0;
                if(exp instanceof ArithmeticExp){
                    switch (((ArithmeticExp) exp).getOperator()){
                        case ADD:
                            v = a + b;
                            break;
                        case SUB:
                            v = a - b;
                            break;
                        case MUL:
                            v = a * b;
                            break;
                        case DIV:
                            if(b==0){
                                return Value.getUndef();
                            }
                            else{
                                v = a/b;
                            }
                            break;
                        case REM:
                            if(b==0){
                                return Value.getUndef();
                            }
                            else{
                                v = a%b;
                            }
                            break;
                        default:
                            assert (false):"error";
                    }
                }
                else if(exp instanceof BitwiseExp){
                    switch (((BitwiseExp) exp).getOperator()){
                        case OR :
                            v = a | b;
                            break;
                        case AND:
                            v = a & b;
                            break;
                        case XOR:
                            v = a^b;
                            break;
                        default:
                            assert (false):"error";
                    }
                }
                else if(exp instanceof ConditionExp){
                    assert false : "bug";
                    switch (((ConditionExp) exp).getOperator()){
                        case EQ :
                            if(a==b){
                                v = 1;
                            }
                            else{
                                v = 0;
                            }
                            break;
                        case NE:
                            if(a!=b){
                                v = 1;
                            }
                            else{
                                v = 0;
                            }
                            break;
                        case GE:
                            if(a>=b){
                                v = 1;
                            }
                            else{
                                v = 0;
                            }
                            break;
                        case GT:
                            if(a>=b){
                                v = 1;
                            }
                            else{
                                v = 0;
                            }
                            break;
                        case LE:
                            if(a<=b){
                                v = 1;
                            }
                            else{
                                v = 0;
                            }
                            break;
                        case LT:
                            if(a<b){
                                v = 1;
                            }
                            else{
                                v = 0;
                            }
                            break;
                        default:
                            assert (false):"error";
                    }
                }
                else if(exp instanceof ShiftExp){
                    switch (((ShiftExp) exp).getOperator()){
                        case SHL :
                            v = a<<b;
                            break;
                        case SHR:
                            v = a>>b;
                            break;
                        case USHR:
                            v = a>>>b;
                            break;
                        default:
                            assert (false):"error";
                    }
                }
                Value res = Value.makeConstant(v);
                return res;
            }
            else{
                return Value.getUndef();
            }


        }
        return Value.getNAC();
    }
}
