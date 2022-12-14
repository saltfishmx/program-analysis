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

package pascal.taie.analysis.dataflow.inter;

import jas.CP;
import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JMethod;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;
    private  PointerAnalysisResult pta;
    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return out.copyFrom(in);
    }
    private  Value getInstanceValue(InstanceFieldAccess ia, CPFact in){
        Value v = Value.getUndef();
        Set<Var> aliasset = new HashSet<>();

        Var base = ia.getBase();
        Set<Obj> baseobj = pta.getPointsToSet(base);
        for(Var alias:pta.getVars()){
            Set<Obj> aliasobjset = new HashSet<>();
            aliasobjset.addAll(pta.getPointsToSet(alias));
            aliasobjset.retainAll(baseobj);
            if(!aliasobjset.isEmpty()){
                aliasset.add(alias);
            }
        }
        for(Var alias:aliasset){
            List<StoreField> sfs = alias.getStoreFields();
            for(StoreField sf:sfs){
                if(sf.getFieldRef().resolve().equals(ia.getFieldRef().resolve())){
                    CPFact fact = solver.getResult().getInFact(sf);
                    if(fact!=null){
                        v = cp.meetValue(v,fact.get(sf.getRValue()));
                    }
                }

            }
        }
        return v;
    }

    private Value getStaticValue(StaticFieldAccess sa,CPFact in){
        Value v = Value.getUndef();
        List<Stmt> stmts = solver.getStmtList();
        for(Stmt stmt:stmts){
            if(stmt instanceof StoreField){
                FieldAccess left = ((StoreField) stmt).getFieldAccess();
                if(left.getFieldRef().equals(sa.getFieldRef())){
                    CPFact fact = solver.getResult().getInFact(stmt);
                    if(fact!=null){
                        Value staticvalue = fact.get(((StoreField) stmt).getRValue());
                        v = cp.meetValue(v,staticvalue);
                    }
                }
            }
        }
        return v;
    }

    private Value getArrayValue(ArrayAccess aa,CPFact in){
        Value v = Value.getUndef();
        Var base = aa.getBase();
        Set<Obj> baseobjset= pta.getPointsToSet(base);
        Set<Var> aliasset = new HashSet<>();
        for (Var alias:
             pta.getVars()) {
             Set<Obj> aliasobjset = new HashSet<>();
             aliasobjset.addAll(pta.getPointsToSet(alias));
             aliasobjset.retainAll(baseobjset);
             if(!aliasobjset.isEmpty()){
                 aliasset.add(alias);
             }
        }
        for(Var alias:aliasset){
            List<StoreArray> sa = alias.getStoreArrays();
            for(StoreArray s : sa){
                Value i = in.get(aa.getIndex());
                Value j;
                CPFact fact = solver.getResult().getInFact(s);
                if(fact!=null){
                    j = fact.get(s.getArrayAccess().getIndex());
                    if(j.isConstant()&&i.isConstant()&&(j.getConstant()==i.getConstant())){
                        v = cp.meetValue(v,fact.get(s.getRValue()));
                    }
                    else if(i.isNAC()||j.isNAC()){
                        v = cp.meetValue(v,fact.get(s.getRValue()));
                    }
                }
            }
        }
        return v;
    }
    private boolean handleArray(Stmt stmt,CPFact in){
        if(stmt.getDef().isPresent()&& stmt.getUses().size()==3 && stmt.getUses().get(2) instanceof ArrayAccess){
            Var def= (Var) stmt.getDef().get();
            in.update(def,getArrayValue((ArrayAccess) stmt.getUses().get(2),in));
            return true;
        }
        else {
            return false;
        }
    }
    private boolean handleStatic(Stmt stmt,CPFact in){
        if(stmt.getDef().isPresent()&&  stmt.getUses().get(0) instanceof StaticFieldAccess){
            Var def= (Var) stmt.getDef().get();
            in.update(def,getStaticValue((StaticFieldAccess) stmt.getUses().get(0),in));
            return true;
        }
        else {
            return false;
        }
    }
    private boolean handleInstance(Stmt stmt,CPFact in){
        if(stmt.getDef().isPresent()&& stmt.getUses().size()==2 && stmt.getUses().get(1) instanceof InstanceFieldAccess){
            Var def= (Var) stmt.getDef().get();
            in.update(def,getInstanceValue((InstanceFieldAccess) stmt.getUses().get(1),in));
            return true;
        }
        else {
            return false;
        }
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        boolean arrayhandled = handleArray(stmt,in);
        boolean statichandled = handleStatic(stmt,in);
        boolean instancehandled = handleInstance(stmt,in);
        if(arrayhandled||statichandled||instancehandled){
            return out.copyFrom(in);
        }
        else{
            return cp.transferNode(stmt,in,out);
        }

    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        Stmt src = edge.getSource();
        if(!src.getDef().isPresent()){
            return out.copy();
        }
        else{
            LValue v =src.getDef().get();
            if(v instanceof Var){
                CPFact res = out.copy();
                res.remove((Var) v);
                return res;
            }
        }
        assert false:"error in calltoreturn";
        return null;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        CPFact res = new CPFact();
        Invoke src = (Invoke) edge.getSource();
        InvokeExp exp = src.getInvokeExp();
        List<Var> args= exp.getArgs();
        List<Var> params = edge.getCallee().getIR().getParams();
        for(int i=0;i<args.size();i++){
            res.update(params.get(i),callSiteOut.get(args.get(i)));
        }
        //b = add(a)  / a =  6
        //int add(int x) / x=6
        //parameters是我们在定义函数的时候，写在括号里面的参数名，而arguments是我们在调用函数的时候，传进去的具体值。

        return res;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact res = new CPFact();
        Stmt des = edge.getCallSite();
        //des =edge.getTarget();
        if(des.getDef().isPresent()){
            Collection<Var> returnVars = edge.getReturnVars();//the variables that hold the return values.
            Value vl = Value.getUndef();
            Var left = (Var) des.getDef().get();;
            for(Var v : returnVars){
                vl = cp.meetValue(vl,returnOut.get(v));
            }
            if(!vl.isUndef()){
                res.update(left,vl);
            }
        }
        return res;
    }
}
