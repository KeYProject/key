package org.key_project.keyide.ui.test.util;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;

// TODO: Document class TreeViewerIterator
public class TreeViewerIterator {
   private List<TreeItem> treeItemList = new LinkedList<TreeItem>();
   
   public TreeViewerIterator(TreeViewer viewer){
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
      
   public List<TreeItem> getList(){
      return treeItemList;
   }
}
