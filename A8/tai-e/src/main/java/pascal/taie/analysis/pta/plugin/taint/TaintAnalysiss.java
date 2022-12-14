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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }
    public Obj getTaintObj(Stmt stmt){
        if(stmt instanceof Invoke){
            for(Source s:config.getSources()){
                if(s.method().equals(((Invoke) stmt).getInvokeExp().getMethodRef().resolve())&&
                s.type().equals(((Invoke) stmt).getRValue().getType())){
                    Obj taintobj = manager.makeTaint((Invoke) stmt,s.type());
                    return taintobj;
                }
            }
        }

        return null;

    }
    public TaintTransfer findtainttransfer(Invoke invoke,int from,int to,CSObj recvobj){
        for(TaintTransfer t:config.getTransfers()){
            JMethod m;
//            if(invoke.isStatic()){
//                m = invoke.getMethodRef().resolve();
//            }
//            else{
//                m = solver.resolveCallee(recvobj,invoke);
//            }
            m = invoke.getMethodRef().resolve();
            if(t.method().equals(m)&&t.to()==to&&t.from()==from){
                return t;
            }
        }
        return  null;
    }
    public  Map<Pointer,PointsToSet> taintpropagate(CSVar csv, CSObj co, JMethod m){
        Map map = new HashMap<>();
        if(!manager.isTaint(co.getObject())){
            return map;
        }
        Obj o = co.getObject();
        Context c = co.getContext();
        //base to result
        for(Invoke invoke:csv.getVar().getInvokes()){//-1 表示 base 变量；-2 表示接收结果的变量。
            TaintTransfer t = findtainttransfer(invoke,-1,-2,co);

            if(t!=null){
                InvokeExp ie = invoke.getInvokeExp();
                if(ie instanceof InvokeInstanceExp){
                    if(((InvokeInstanceExp) ie).getBase().equals(csv.getVar())){
                        CSObj taintobj = csManager.getCSObj(c,manager.makeTaint(manager.getSourceCall(o),t.type()));
                        if(invoke.getLValue()!=null){
                            CSVar left = csManager.getCSVar(csv.getContext(),invoke.getLValue());
                            map.put(left, PointsToSetFactory.make(taintobj));
                        }
                    }

                }
            }
        }
        //args to base/result
        m.getIR().forEach(stmt -> {
            if(stmt instanceof Invoke){
                Invoke invoke = (Invoke) stmt;
                int argnum = invoke.getInvokeExp().getArgCount();
                for (int i=0;i<argnum;i++){
                    TaintTransfer atob = findtainttransfer(invoke,i,-1,co);
                    TaintTransfer ator = findtainttransfer(invoke,i,-2,co);
                    InvokeExp ie = invoke.getInvokeExp();
                    if(atob!=null&&ie.getArgs().get(i).equals(csv.getVar())){
                        CSObj taintobj = csManager.getCSObj(c,manager.makeTaint(manager.getSourceCall(o),atob.type()));

                        if(ie instanceof InvokeInstanceExp){
                            CSVar base = csManager.getCSVar(csv.getContext(),((InvokeInstanceExp) ie).getBase());
                            map.put(base,PointsToSetFactory.make(taintobj));
                        }
                    }
                    if(ator!=null&&ie.getArgs().get(i).equals(csv.getVar())){
                        CSObj taintobj = csManager.getCSObj(c,manager.makeTaint(manager.getSourceCall(o),ator.type()));
                        if(invoke.getLValue()!=null){
                            CSVar left = csManager.getCSVar(csv.getContext(),invoke.getLValue());
                            map.put(left, PointsToSetFactory.make(taintobj));
                        }
                    }
                }
            }
        });
        return map;
    }
    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        //handle sink
        result.getCallGraph().forEach(method->{
            method.getIR().getStmts().forEach(stmt -> {
                if(stmt instanceof Invoke){
                    config.getSinks().forEach(sink -> {
                        if (((Invoke) stmt).getInvokeExp().getMethodRef().resolve().equals(sink.method())){
                            InvokeExp ie = ((Invoke) stmt).getInvokeExp();
                            int i = sink.index();
                            Var taintvar = ie.getArgs().get(i);
                            Set<Obj> taintobj = result.getPointsToSet(taintvar);
                            for(Obj o : taintobj){
                                if(manager.isTaint(o)){
                                    taintFlows.add(new TaintFlow(manager.getSourceCall(o), (Invoke) stmt,i));
                                }
                            }
                        }
                    });
                }

            });
        });
        return taintFlows;
    }
}
