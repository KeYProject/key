package org.key_project.keyide.ui.providers;

import org.eclipse.jface.viewers.LabelProvider;
import org.key_project.util.java.ObjectUtil;

//for image
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.graphics.Image;
import org.osgi.framework.Bundle;
import org.osgi.framework.FrameworkUtil;
import de.uka.ilkd.key.proof.Node.NodeIterator;
import java.net.URL;
//

import de.uka.ilkd.key.proof.Node;

/**
 * A class to provide the correct labels for the KeY-Outline.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class OutlineLabelProvider extends LabelProvider {

   /**
    * {@inheritDoc}
    */
   @Override
   public String getText(Object element){
      if(element instanceof Node){
         if(((Node)element).getNodeInfo().getBranchLabel() == null)
            return((Node)element).serialNr() + ":" + ((Node)element).name();
         else return((Node)element).serialNr() + ":" + ((Node)element).name() + ": " + ((Node)element).getNodeInfo().getBranchLabel();
      }
      else if(element instanceof BranchFolder)
         return ((BranchFolder)element).getLabel(); 
      else
         return ObjectUtil.toString(element);
   }
   
 /**
 * {@inheritDoc}
 */
@Override
public Image getImage(Object element) {
   
   final Image FOLDER_IMAGE = getImageFromFile("icons/folder.png");

   final Image FOLDERPROVEN_IMAGE = getImageFromFile("icons/folderproved.png");


   final Image PROOF_IMAGE = getImageFromFile("icons/ekey-mono16.gif");
   
   final Image PROVEN_IMAGE = getImageFromFile("icons/keyproved16.gif");
   
   if(element instanceof Node){
      Node node = (Node)element;
      if(node.parent()!=null&&!node.root()){     
         if(node.name().equals("Closed goal")){
            return PROVEN_IMAGE;
         }
         return PROOF_IMAGE;
      }
   }
   if(element instanceof BranchFolder){
      if(((BranchFolder)element).isProved()){
         return FOLDERPROVEN_IMAGE;
      }
      return FOLDER_IMAGE;
   }
   return PROOF_IMAGE;
}

private static Image getImageFromFile(String file){
   Bundle bundle = FrameworkUtil.getBundle(OutlineLabelProvider.class);
   URL url = FileLocator.find(bundle, new Path(file), null);
   ImageDescriptor image = ImageDescriptor.createFromURL(url);
   return image.createImage();
}

/**
 * Checks if the subtree of the given node is proven. Returns true iff all leaves are proven (Closed goal), false otherwise.
 * @param node
 * @return true iff all leaves proven, false otherwise.
 */
   private boolean subTreeProven(Node node){
      boolean proven = true;
      NodeIterator leaves = node.leavesIterator();
      while(leaves.hasNext()){
       Node leave = leaves.next();
         if(leave.name().equals("OPEN GOAL"))
            proven=false;
   //      System.out.println(leave.name() + " " + proven);
      }
      return proven;
   }
   
   
}
