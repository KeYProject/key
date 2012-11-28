package org.key_project.keyide.ui.views;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.part.IPageSite;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;
import org.key_project.keyide.ui.providers.OutlineContentProvider;
import org.key_project.keyide.ui.providers.OutlineLabelProvider;

import de.uka.ilkd.key.proof.Proof;

public class Outline extends ContentOutlinePage {
   private Proof proof;
   
//   public TreeViewer viewer;
   public Outline(Proof proof) {
      this.proof = proof;
      // TODO Auto-generated constructor stub
   }
   
   @Override
   protected int getTreeStyle() {
      return super.getTreeStyle() | SWT.VIRTUAL;
   }
   
   @Override
   public void createControl(Composite parent) {
      super.createControl(parent);
      getTreeViewer().setUseHashlookup(true);
      getTreeViewer().setContentProvider(new OutlineContentProvider(getTreeViewer()));
      getTreeViewer().setLabelProvider(new OutlineLabelProvider());
      getTreeViewer().setInput(proof);
   }
   
   



//   @Override
//   public void createPartControl(Composite parent) {
//   //   if(KeYToUIUtil.getProof() != null){
//         viewer = new TreeViewer(parent, SWT.VIRTUAL | SWT.BORDER | SWT.SIMPLE);
//         viewer.setContentProvider(new OutlineContentProvider(viewer));
//         viewer.setUseHashlookup(true);
//         viewer.setLabelProvider(new OutlineLabelProvider());
//         viewer.setInput(null);
//    //  }
//   }
//
//   @Override
//   public void setFocus() {
//      // TODO Auto-generated method stub
//
//   }

}
