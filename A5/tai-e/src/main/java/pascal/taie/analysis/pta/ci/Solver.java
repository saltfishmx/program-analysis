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

package pascal.taie.analysis.pta.ci;

import fj.P;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;
import pascal.taie.ir.IR;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;
    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();

        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {//不要忘记在该方法中处理静态字段 loads/stores 和静态方法调用
        // TODO - finish me
        if(!callGraph.contains(method)){
            callGraph.addReachableMethod(method);
            IR ir = method.getIR();
            ir.forEach(stmt->{
                stmt.accept(stmtProcessor);
            });
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(Copy stmt) {
            Var x = stmt.getLValue();
            Var y = stmt.getRValue();
            Pointer px = pointerFlowGraph.getVarPtr(x);
            Pointer py = pointerFlowGraph.getVarPtr(y);
            addPFGEdge(py,px);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(New stmt) {
            Obj o = heapModel.getObj(stmt);
            PointsToSet pts = new PointsToSet(o);
            Var x = stmt.getLValue();
            Pointer pt = pointerFlowGraph.getVarPtr(x);
            workList.addEntry(pt,pts);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadField stmt) {//y = T.f
            if(stmt.isStatic()){
                Var y =stmt.getLValue();
                addPFGEdge(pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()),
                        pointerFlowGraph.getVarPtr(y));
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) {//T.f = y
            if(stmt.isStatic()){
                Var y = stmt.getRValue();
                addPFGEdge(pointerFlowGraph.getVarPtr(y),
                        pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()));
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Invoke stmt) {
            if(stmt.isStatic()){
                JMethod m = stmt.getMethodRef().resolve();
                if(callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt),stmt,m))){
                    //.addReachableMethod(m);
                    addReachable(m);
                    int size = m.getIR().getParams().size();
                    for(int i=0;i<size;i++){
                        addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getInvokeExp().getArg(i)),
                                pointerFlowGraph.getVarPtr(m.getIR().getParam(i)));
                    }
                    for(Var v :m.getIR().getReturnVars()){
                        Var l = stmt.getLValue();
                        if(l!=null){
                            addPFGEdge(pointerFlowGraph.getVarPtr(v),pointerFlowGraph.getVarPtr(l));
                        }

                    }
                }
            }
            return StmtVisitor.super.visit(stmt);
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if(pointerFlowGraph.addEdge(source,target)){
            PointsToSet ptss = source.getPointsToSet();
            if(!ptss.isEmpty()){
                workList.addEntry(target,ptss);
            }
        }
        // TODO - finish me
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while(!workList.isEmpty()){
            WorkList.Entry et =workList.pollEntry();
            Pointer n = et.pointer();
            PointsToSet pts = et.pointsToSet();
            PointsToSet delta = propagate(n,pts);
            if(n instanceof VarPtr){
                Var x = ((VarPtr) n).getVar();
                for (Obj o:
                     delta) {
                    for(StoreField sf:x.getStoreFields()){//x.f = y
                        addPFGEdge(pointerFlowGraph.getVarPtr(sf.getRValue()),
                                pointerFlowGraph.getInstanceField(o,sf.getFieldRef().resolve()));
                    }
                    for(LoadField lf:x.getLoadFields()){// y = x.f
                        addPFGEdge(pointerFlowGraph.getInstanceField(o,lf.getFieldRef().resolve()),
                                pointerFlowGraph.getVarPtr(lf.getLValue()));
                    }
                    for(LoadArray la:x.getLoadArrays()){//y = x[i]
                        addPFGEdge(pointerFlowGraph.getArrayIndex(o),
                                pointerFlowGraph.getVarPtr(la.getLValue()));
                    }
                    for(StoreArray sa:x.getStoreArrays()){ //x[i] = y
                        addPFGEdge(pointerFlowGraph.getVarPtr(sa.getRValue()),
                                pointerFlowGraph.getArrayIndex(o));
                    }
                    processCall(x,o);
                }
            }
        }
        // TODO - finish me
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private  PointsToSet minus(PointsToSet a,PointsToSet b){ // a - b
        PointsToSet res = new PointsToSet();
        for(Obj o:a){
            if(!b.contains(o)){
                res.addObject(o);
            }
        }
        return res;
    }

    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet ptsn = pointer.getPointsToSet();
        PointsToSet delta = minus(pointsToSet,ptsn);
        if(!delta.isEmpty()){
            for(Obj o:delta){
                pointer.getPointsToSet().addObject(o);
            }
            Set<Pointer> set = pointerFlowGraph.getSuccsOf(pointer);
            for (Pointer s:set){
                workList.addEntry(s,delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for(Invoke invoke : var.getInvokes()){
            JMethod m = resolveCallee(recv,invoke);
            Var mthis = m.getIR().getThis();
            workList.addEntry(pointerFlowGraph.getVarPtr(mthis),new PointsToSet(recv));
            if(callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke),invoke,m))){
                addReachable(m);
                int size = m.getIR().getParams().size();
                for(int i=0;i<size;i++){
                    addPFGEdge(pointerFlowGraph.getVarPtr(invoke.getInvokeExp().getArg(i)),
                            pointerFlowGraph.getVarPtr(m.getIR().getParam(i)));
                }
                for(Var v :m.getIR().getReturnVars()){
                    Var l = invoke.getLValue();
                    if(l!=null){
                        addPFGEdge(pointerFlowGraph.getVarPtr(v),pointerFlowGraph.getVarPtr(l));
                    }

                }

            }
        }
        // TODO - finish me
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
