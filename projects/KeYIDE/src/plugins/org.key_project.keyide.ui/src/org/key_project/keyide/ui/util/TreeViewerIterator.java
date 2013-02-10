package org.key_project.keyide.ui.util;

import java.util.LinkedList;

import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;
import org.key_project.keyide.ui.providers.BranchFolder;

import de.uka.ilkd.key.proof.Node;

public class TreeViewerIterator {

   TreeViewer viewer;
   LinkedList<TreeItem> treeItemList = new LinkedList<TreeItem>();
   
   public TreeViewerIterator(TreeViewer viewer){
      this.viewer = viewer;
      viewer.expandAll();
      treeToList(viewer.getTree());
   }
   
   private void treeToList(Tree tree){
      TreeItem[] items = tree.getItems();
      iterateTree(items);
   }
   
   private void iterateTree(TreeItem[] items){
      for(TreeItem item : items){
         treeItemList.add(item);
         TreeItem[] children = item.getItems();
         iterateTree(children);
      }
   }
   
   public boolean hasNext(){
      if(!treeItemList.isEmpty()){
         return true;
      }
      else return false;
   }
   
   public TreeItem next(){
      TreeItem item = null;
      if(!treeItemList.isEmpty()){
         item = treeItemList.get(0);
         treeItemList.remove(0);
         
      }
      return item;
   }
      
   public LinkedList<TreeItem> getList(){
      return treeItemList;
   }
}
