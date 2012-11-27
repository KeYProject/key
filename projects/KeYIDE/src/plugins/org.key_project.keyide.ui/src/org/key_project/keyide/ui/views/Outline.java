package org.key_project.keyide.ui.views;

import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.part.ViewPart;
import org.key_project.keyide.ui.providers.OutlineContentProvider;
import org.key_project.keyide.ui.providers.OutlineLabelProvider;

public class Outline extends ViewPart {
   public static TreeViewer viewer;
   public Outline() {
      // TODO Auto-generated constructor stub
   }

   @Override
   public void createPartControl(Composite parent) {
   //   if(KeYToUIUtil.getProof() != null){
         viewer = new TreeViewer(parent, SWT.VIRTUAL | SWT.BORDER | SWT.SIMPLE);
         viewer.setContentProvider(new OutlineContentProvider(viewer));
         viewer.setUseHashlookup(true);
         viewer.setLabelProvider(new OutlineLabelProvider());
         viewer.setInput(null);
    //  }
   }

   @Override
   public void setFocus() {
      // TODO Auto-generated method stub

   }

}
