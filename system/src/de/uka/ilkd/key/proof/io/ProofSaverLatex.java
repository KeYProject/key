// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.proof.io;

import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Iterator;

import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;


public class ProofSaverLatex extends ProofSaver {


   public ProofSaverLatex(Proof proof, String filename, String internalVersion) {
      super(proof, filename,internalVersion);
   }
   
   
   public String save() throws IOException{
      String errorMsg = null;
      FileOutputStream fos = null;
      PrintStream ps = null;
      try {
          fos = new FileOutputStream(filename);
          ps = new PrintStream(fos);
          StringBuffer tree=new StringBuffer();
          Node root = proof.root();
          
          ps.println(texHeader());
          ps.println("\\pstree[treemode=R,treealign=down,treefit=loose,");
          ps.println("        treesep=0.3,levelsep=1,nodesep=0.1]{\\Tn}");
          ps.println("{\n"+TRNode(root));
          ps.print(collectProof(root.childrenIterator(),
                                root.childrenCount(),
                                "",tree)); 
                                
          ps.println("}");
          ps.println("\\end{document}");

      } catch (IOException ioe) {
          errorMsg = "Could not save \n"+filename+".\n";
          errorMsg += ioe.toString();	    
      } catch (NullPointerException e) {
          errorMsg = "Could not save \n"+filename+"\n";
          errorMsg += "No proof present?";
          e.printStackTrace();
      } finally {
         // try {
	      if (fos != null) fos.close();
          //} catch (IOException ioe) {
	//     mediator.notify(new GeneralFailureEvent("IO Error: "+ioe));
          //}          
      }	   
      return errorMsg; // null if success
   }
   
   
   String nodeSeqToString(Node node) {
      LogicPrinter logicPrinter = 
         new LogicPrinter(new ProgramPrinter(null), 
	                  new NotationInfo(),
	                  node.proof().getServices(),
	                  true);
      logicPrinter.printSequent(node.sequent());
      StringBuffer buf = logicPrinter.result();
      for (int i=0; i<buf.length(); i++) {
         char c = buf.charAt(i);
         if ( c=='{' || c=='}' || c=='&' || c=='%' ) {
            buf.insert(i,'\\');
            i++;
         }
      }
      return buf.toString().replace('\n',' ');
   }
   

   private String TRNode(Node node) {
      return "\\TR[href=-1]{\\lstinline$"+nodeSeqToString(node)+"$}\n";
   }



   private StringBuffer collectProof(Iterator<Node> it, int siblings,
                                     String prefix, StringBuffer tree) {       

      Node node;

      if (siblings==0) return tree;

      if (siblings==1) {
         node = it.next();
         tree.append(prefix+TRNode(node));
         collectProof(node.childrenIterator(), node.childrenCount(), 
            prefix, tree);
      } else {
         int i=0;
         while (it.hasNext()) {
            i++;
            node = it.next();
            tree.append(prefix+"\\pstree{\\TR{Case "+i+"}}\n");
            tree.append(prefix+"       {\\Tn ");
            tree.append(prefix+"        "+TRNode(node));
            collectProof(node.childrenIterator(), node.childrenCount(), 
               prefix+"        ", tree);
            tree.append(prefix+"       }\n");
         }
      }
      return tree;
   }
   
   private StringBuffer texHeader() {
      java.net.URL header = 
      de.uka.ilkd.key.util.KeYResourceManager.getManager().getResourceFile(
         ProofSaverLatex.class, "proofheader.tex"); 
      StringBuffer sb=new StringBuffer(8000);
      sb.append("% "+proof.name()+"\n");
      try {
	  FileInputStream inp=new FileInputStream(header.getFile());
	  while (inp.available()>0) sb.append((char)inp.read());
	  inp.close();
      } catch (IOException ioe) {
	  sb=new StringBuffer("% Could not find proofheader.tex\n");
      }
      return sb;
   }
}
