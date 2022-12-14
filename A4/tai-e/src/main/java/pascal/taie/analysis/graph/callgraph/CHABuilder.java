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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }
    private Collection<Invoke> getAllCallSites(JMethod m){
        Collection<Invoke> allcs=new HashSet<>();

        if(m.isAbstract()){
            return allcs;
        }
        IR ir=m.getIR();
        ir.forEach(stmt->{
            if(stmt instanceof Invoke){
                allcs.add((Invoke) stmt);
            }
        });
        return allcs;
    }
    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        Set<JMethod> rm = new HashSet<>();
        Queue<JMethod> wl = new LinkedList<>();
        wl.add(entry);
        while(!wl.isEmpty()){
            JMethod m = wl.remove();
            if(!rm.contains(m)){
                rm.add(m);
                for(Invoke cs : getAllCallSites(m)){
                    Set<JMethod> T = resolve(cs);
                    for(JMethod tm : T){
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(cs),cs,tm));
                        wl.add(tm);
                    }
                }
            }
        }
        for(JMethod m : rm){
            callGraph.addReachableMethod(m);
        }
        // TODO - finish me
        return callGraph;
    }
    private Set<JClass> getallsubclass(JClass c){
        Set<JClass> T = new HashSet<>();
        T.add(c);
        Collection<JClass> cl = hierarchy.getDirectSubclassesOf(c);
        for(JClass i : cl){
            T.addAll(getallsubclass(i));
        }
        return  T;
    }
    private Set<JClass> getallsubinterfaces(JClass c){
        Set<JClass> T = new HashSet<>();
        assert c.isInterface():"not a interface";
        T.add(c);
        Collection<JClass> cl = hierarchy.getDirectSubinterfacesOf(c);
        for(JClass i : cl){
            T.addAll(getallsubinterfaces(i));
        }
        return  T;
    }
    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> T=new HashSet<>();
        MethodRef methodRef=callSite.getMethodRef();
        Subsignature m=methodRef.getSubsignature();
        JClass c= methodRef.getDeclaringClass();

        if(callSite.isStatic()){
            T.add(c.getDeclaredMethod(m));
        }
        else if(callSite.isSpecial()){
            JMethod _t=dispatch(c,m);
            if(_t!=null)
                T.add(dispatch(c,m));
        }
        else if(callSite.isVirtual()){
            Collection<JClass> subclasses=getallsubclass(c);
            for(JClass item:subclasses){
                JMethod _t=dispatch(item,m);
                if(_t!=null)
                    T.add( dispatch(item,m));
            }
        }
        else if (callSite.isInterface()){
            //implements of (interface and sub interfaces) and subclasses
            Collection<JClass> subInterfaces=getallsubinterfaces(c);
            Collection<JClass> _implements=new HashSet<>();
            for(JClass _interface: subInterfaces){
                _implements.addAll(hierarchy.getDirectImplementorsOf(_interface));
            }
            Collection<JClass> subclasses=new HashSet<>();
            for(JClass directImplement:_implements){
                subclasses.addAll(getallsubclass(directImplement));
            }

            for(JClass item:subclasses){
                JMethod _t=dispatch(item,m);
                if(_t!=null)
                    T.add(dispatch(item,m));
            }
        }

        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        JMethod res = jclass.getDeclaredMethod(subsignature);
        if(res!=null&&!res.isAbstract()){
            return res;
        }
        else{
            JClass sup = jclass.getSuperClass();
            if(sup==null){
                return null;
            }
            else{
                return dispatch(sup,subsignature);
            }
        }
    }
}
