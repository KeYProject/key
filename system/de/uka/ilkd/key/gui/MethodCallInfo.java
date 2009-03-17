// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.gui;

import java.util.*;

/**
 * This is a utility class that helps to monitor the invocation of methods during
 * the execution of the system and to indirectly monitor partial memory consumption
 * by monitoring calls to constructors and the finalize() method. This class
 * has counters that record HOW OFTEN a method was called.
 * @author gladisch
 */
public class MethodCallInfo {
    /**A global flag that activates the counting of method calls when set to true.
     * This feature will be used in unit testing of KeY to test against memory leaks. */
    public static boolean MethodCallCounterOn = false;
    
    public static final String Method = "Method:";
    public static final String constructor = Method+"Constructor";
    public static final String finalize = Method+"finalize()";
    public static final String addOrPut = Method+"add() or put ()";
    public static final String remove = Method+"remove()";
    public static final String clear = Method+"clear()";
    /**Do not reset this instance */
    public static final MethodCallInfo Global =  new MethodCallInfo("Global");
    /**Reset this instance to compare different states of the system */
    public static final MethodCallInfo Local =  new MethodCallInfo("Local");
    
    /** Maps a Class or an identifier of a concrete Object (e.g. a static collection) to a counter object*/
    protected ContextCounter counter;
    
    protected String name="";
    MethodCallInfo(){
        reset();
    }
    
    MethodCallInfo(String name){
        reset();
        this.name = name;
    }
    
    public void reset(){
        counter = new ContextCounter();
    }
    
    /**Increment the counter for the specified method {@code methodName} of class {@code className} */
    public Integer incForClass(String className, String methodName){
        Vector context = new Vector(2);
        context.add(className);
        context.add(methodName);
        counter.inc(context.iterator());
        //context describes a "path" to the actual counter
        return counter.get(context.iterator());
    }
  
    /**Increment the counter for the specified method {@code methodName} of object {@code objName} */
    public Integer incForObject(String objName, String methodName){
        //context describes a "path" to the actual counter
        Vector context = new Vector(2);
        context.add(objName);
        context.add(methodName);
        counter.inc(context.iterator());
        return counter.get(context.iterator());
    }
    
    public static String indent(int n){
        String res = "";
        for(int i=0;i<n;i++){
            res += " ";
        }
        return res;
    }

    public String toString(){
        return "---- ("+name+") MethodCallInfo ----"+counter.toString(1)+"\n";
    }

    public abstract class Counter<C>{
        /**Returns the number that is set. The context is part of the call stack of the invoked method.*/
        public abstract Integer set(C context, int val);
        /**The context is part of the call stack of the invoked method. */
        public abstract Integer get(C context);
        /**Increment, The context is part of the call stack of the invoked method. */
        public Integer inc(C context){
            C contextClone;
            if(context instanceof ClonableIterator){
                contextClone = (C)((ClonableIterator)context).clone();
            }else if(context instanceof Iterator){
                throw new RuntimeException("Parameter context must be immutable.");
            }else{
                contextClone = context;
            }
            Integer num = get(context);
            if(num==null)
                num = 0;
            return set(contextClone, num +1);
        };
        public String toString(int indent){return "?";};
    };
    
    public class IntCounter extends Counter<Object>{
        /**Counts how often a method is called. It does not distinguish between different contexts of invocation as it is just one integer. */
        int i;
        /**Set context to null because this Counter is independent from the context of method invocation */
        public Integer set(Object context, int val){
            assert context==null;
            i = val;
            return i;
        };

        /**Set context to null because this Counter is independent from the context of method invocation */
        public  Integer get(Object context){
            assert context==null;
            return i;
        }
        /**Increments the attribute i. Set context to null because this Counter is independent from the context of method invocation. */
        public Integer inc(Object context){
            assert context==null;
            return set(context, get(context)+1);
        }
    }
    
    private class ClonableIterator implements Iterator {
        AbstractList list;
        int pos=-1;
        public ClonableIterator(AbstractList al){
            list=al;
        }
        public boolean hasNext() {
            if(list.size()>pos+1){
                return true;
            }
            return false;
        }
        public Object next() {
            return list.get(++pos);
        }
        public void remove() {
            list.remove(pos);
        }
        
        public ClonableIterator clone(){
            ClonableIterator res = new ClonableIterator(list);
            res.pos = this.pos;
            return res;
        }
    }
   
    /**Realizes a hierarchical organization of counters. 
     * The iterator describes a path to the number that counts invocations, 
     * e.g., class->object->CallerMethod->CalledMethod */
    public class ContextCounter extends Counter<Iterator>{
        /**Counts how often a method is called. It does distinguish between different contexts of invocation . */
        HashMap<Object,Counter> contextItemToCounter;
        /**If this counter is a leaf, then the number is saved here. */
        Integer i=null;
        
        ContextCounter(){
            contextItemToCounter = new HashMap<Object,Counter>();
        }
        
        /**Set context to null because this Counter is independent from the context of method invocation */
        public Integer set(Iterator context, int val){
            assert context !=null;
            if(context.hasNext()){
                Object contextItem = context.next();
                Counter child = contextItemToCounter.get(contextItem);
                if(child==null){
                    child = new ContextCounter();
                    contextItemToCounter.put(contextItem,child);
                }
                //at this point the iterator context has been iterated by one position
                return child.set(context, val); 
            }else{
                i = val;
                return i;
            }
        };

        public  Integer get(Iterator context){
            if(context!=null && context.hasNext()){
                Object contextItem = context.next();
                Counter child = contextItemToCounter.get(contextItem);
                if(child==null){
                    return null;
                }else{
                    return child.get(context);
                }
            }else{
                return i;
            }
        }
        
        public Integer inc(Iterator context){
            assert context !=null;
            if(context.hasNext()){
                Object contextItem = context.next();
                Counter child = contextItemToCounter.get(contextItem);
                if(child==null){
                    child = new ContextCounter();
                    contextItemToCounter.put(contextItem,child);
                }
                //at this point the iterator context has been iterated by one position
                return child.inc(context); 
            }else{
                i = i==null?1:i+1;
                return i;
            }
        };

        public String toString(int indent){
            String res="";
            if(i !=null){
                res += ":"+i;
            }
            if(contextItemToCounter!=null && contextItemToCounter.size()>0){
                for(Map.Entry<Object, Counter> e:contextItemToCounter.entrySet()){
                    res +=  "\n" +indent(indent)+ e.getKey() + e.getValue().toString(indent+2);
                }
                if(contextItemToCounter.containsKey(MethodCallInfo.constructor)&&
                        contextItemToCounter.containsKey(MethodCallInfo.finalize)){
                    int diff = contextItemToCounter.get(MethodCallInfo.constructor).get(null)-
                                contextItemToCounter.get(MethodCallInfo.finalize).get(null);
                    res +=  "\n" + indent(indent) + "Constructed but not finalized objects:"+diff;
                }
                if(contextItemToCounter.containsKey(MethodCallInfo.addOrPut)&&
                        contextItemToCounter.containsKey(MethodCallInfo.remove)){
                    int diff = contextItemToCounter.get(MethodCallInfo.addOrPut).get(null)-
                                contextItemToCounter.get(MethodCallInfo.remove).get(null);
                    res +=  "\n" +indent(indent) + "Added but not removed items:"+diff;
                }
            }
            return res;
        }
        
    }
    
}
