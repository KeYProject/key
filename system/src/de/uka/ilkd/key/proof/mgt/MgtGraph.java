// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

//package de.uka.ilkd.key.proof.mgt;
//
//import java.util.*;
//import de.uka.ilkd.key.util.GraphViz;
//import de.uka.ilkd.key.proof.*;
//import de.uka.ilkd.key.proof.init.*;
//import de.uka.ilkd.key.speclang.*;
//import de.uka.ilkd.key.logic.op.*;
//import de.uka.ilkd.key.java.abstraction.KeYJavaType;

/*
 * Is this code still in use?
 * No reference to this class could be detected outside this file.
 * 
 * This class would have to be adapted to the new naming scheme for contracts. 
 */

//public class MgtGraph {
//
//    Map<Object,MgtNode> nodes = new HashMap();
//    Set<MgtEdge> edges = new HashSet();
//    
//    public void addNode(Object o, String ... attrs) {
//        if (nodes.containsKey(o)) {
//	    System.out.println("Dupe node "+o.getClass());
//	} else {
//            nodes.put(o, new MgtNode(o, attrs));
//	}
//    }
//
//    public void addEdge(Object f, Object t, String ... s) {
//        MgtEdge e = new MgtEdge(f,t,s);
//        addNode(f);
//        addNode(t);
//        edges.add(e);
//	if (nodes.containsKey(f)) nodes.get(f).addOutEdge(e);
//	if (nodes.containsKey(t)) nodes.get(t).addInEdge(e);
//    }
//
//    
//    public void visualize() {
//        propagate();
//    	GraphViz gv = new GraphViz();
//	gv.addln(gv.start_graph());
//
//        String classRank = "{rank = source";
//        String proofRank = "{rank = sink";
//        String specRank = "{rank = same";
//
//	for (Object o: nodes.keySet()) {
//	    if (o instanceof IProgramMethod) continue; // these are part of class
//	
//	    gv.addln(node(o)+nodes.get(o).printAttrs());
//
//	    if (o instanceof Proof)
//	        proofRank = proofRank +" "+node(o);
//            else if (o instanceof KeYJavaType)
//	        classRank = classRank+" "+ node(o);
//	    else if (o instanceof FunctionalOperationContract)
//	        specRank = specRank +" " + node(o);
//	    else if (o instanceof ClassInvariant)
//	        specRank = specRank +" " + node(o);
//	}
//	
//	for (MgtEdge e: edges) {
//	    gv.addln(port(e.from())+"->"+port(e.to())+e.printAttrs());
//	}
//
//        gv.addln(classRank+"}");
//        gv.addln(proofRank+"}");
//        gv.addln(specRank+"}");
//	gv.addln(gv.end_graph());
////	System.out.println(gv.getDotSource());
//	java.io.File out = new java.io.File("key-mgt.ps");
//	gv.writeGraphToFile(gv.getGraph(gv.getDotSource()), out);
//    }
//    
//    
//    private void propagate() {
//	boolean changed = false;
//	do {
//	    changed = false;
//	    //rules may not be idempotent (or we loop forever)
//	    //locally closed proofs with no open deps are globally closed
//            for (Object o: nodes.keySet()) {
//		MgtNode n = nodes.get(o);
//		if (o instanceof Proof && 
//		        n.getAttr("color").equals("green") &&
//			!n.getAttr("style").contains("filled")) {
//	            //check dependencies
//		    boolean allDepFilled = true;
//		    for (MgtEdge e: n.incoming()) {
//	        	if (!nodes.get(e.from()).
//		        	getAttr("style").contains("filled")) {
//		            allDepFilled = false;
//			    break;
//	        	}
//		    }
//		    if (allDepFilled) {
//		        n.addAttr("style=filled","fillcolor=green",
//			          "color=black");
//			changed = true;
//		    }
//		}
//	    }
//	    for (MgtEdge e: edges) {
//	        MgtNode f = nodes.get(e.from());
//		MgtNode t = nodes.get(e.to());
//		//POs with a globally closed proof are closed
//	        if ((f.getContent() instanceof Proof) && 
//			f.getAttr("fillcolor").equals("green") &&
//			f.getAttr("style").contains("filled") &&
//			!t.getAttr("style").contains("filled")) {
//		    t.addAttr("style=filled","fillcolor=green");
//		    changed = true;
//		}
//		//things assoc. with a closed PO are closed
//	        if ((!(f.getContent() instanceof Proof)) && 
//			t.getAttr("fillcolor").equals("green") &&
//			t.getAttr("style").contains("filled") &&
//			!f.getAttr("style").contains("filled")) {
//		    f.addAttr("style=filled","fillcolor=green");
//		    changed = true;
//		}
//		//things with dirty deps are themselves dirty
//		//but a dirty proof does not make the PO dirty
//	        if (f.getAttr("style").contains("dashed") &&
//			!t.getAttr("style").contains("dashed") &&
//			!(f.getContent() instanceof Proof)) {
//		    t.addAttr("style=dashed");
//		    changed = true;
//		}
//		//proofs for dirty POs are dirty
//	        if (t.getAttr("style").contains("dashed") &&
//			!f.getAttr("style").contains("dashed") &&
//			(f.getContent() instanceof Proof)) {
//		    f.addAttr("style=dashed");
//		    changed = true;
//		}
//	    }
//	} while (changed);
//    }
//
//
//    private String recordLabel(ProgramMethod pm) {
//        StringBuffer sb = new StringBuffer(pm.getName());
//        sb.append("(");
//        for (int i = 0, n = pm.getParameterDeclarationCount();
//             i < n; i++) {
//            sb.append(pm.getParameterDeclarationAt(i)).append(", ");
//        }
//        if (pm.getParameterDeclarationCount() > 0) {
//            sb.setLength(sb.length() - 2);
//        }
//        sb.append(")");
//        return "<"+pm.hashCode()+"> "+
//			    sb.toString().replace('<',' ').replace('>',' ');
//    }
//
//
//    private String recordLabel(KeYJavaType kjt) {
//        return "<"+kjt.hashCode()+"> "+kjt.getName()+"";
//    }
//    
//    private String label(Proof p) {
//        return "Proof"+p.name().toString().
//	    replace(", JML normal_behavior operation contract","").
//	    replace("EnsuresPost","");
//    }
//
//    
//    private String node(Object o) {
//        if (o instanceof Proof)
//	    return ""+o.hashCode();
//	else if (o instanceof FunctionalOperationContract)
//	    return "\""+((FunctionalOperationContract)o).getName().
//	        replace("normal_behavior operation contract", "ct")+"\"";
//	else if (o instanceof ClassInvariant)
//	    return "\""+((ClassInvariant)o).getDisplayName().
//	        replace("class invariant","inv")+"\"";
//	else if (o instanceof KeYJavaType) 
//	    return "\""+((KeYJavaType)o).getName()+"\"";
//	else if (o instanceof ProofOblInput)
//	    return "\""+((ProofOblInput)o).name().
//	        replace(", JML normal_behavior operation contract","")+"\"";
//	else {
//	    System.out.println("Unknown node class "+o.getClass());
//	    return "XXX";
//	}
//    }
//
//    
//    private String port(Object o) {
//        if (o instanceof KeYJavaType)
//	    return ((KeYJavaType)o).getName()+":"+((KeYJavaType)o).hashCode();
//	else if (o instanceof IProgramMethod)
//	    return ((IProgramMethod)o).getContainerType().getName()+":"+
//	        ((IProgramMethod)o).hashCode();
//        else return node(o);
//    }
//    
//    
//}
