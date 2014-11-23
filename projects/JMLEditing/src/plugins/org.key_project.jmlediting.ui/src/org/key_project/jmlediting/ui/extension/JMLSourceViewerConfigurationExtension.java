package org.key_project.jmlediting.ui.extension;
import java.util.LinkedList;
import java.util.ListIterator;

import org.eclipse.jdt.internal.ui.text.JavaPresentationReconciler;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.ui.texteditor.ITextEditor;
import org.key_project.javaeditor.extension.DefaultJavaSourceViewerConfigurationExtension;
import org.key_project.javaeditor.extension.IJavaSourceViewerConfigurationExtension;

/**
 * An {@link IJavaSourceViewerConfigurationExtension} to support JML.
 * 
 * @author Martin Hentschel
 */
   
public class JMLSourceViewerConfigurationExtension extends
      DefaultJavaSourceViewerConfigurationExtension {
   
   
   IDocument document;      
      
   public JMLSourceViewerConfigurationExtension(){
      
   }
   /**
    * seeks the Documents text for JML Multi Line comments
    * 
    * @return A Linked List of JML Comment sections
    */
   public LinkedList<Comment> findCommentOffsets() {
      String text = document.get();
      int lastIndex = 0;
      int begin;
      int end;
      LinkedList<Comment> comments = new LinkedList<Comment>();
      while (lastIndex > -1) {
         begin = text.indexOf("/*@", lastIndex);
         if (begin > -1)                           //Stop searching When End of File is reached
            lastIndex = begin;
         else
            return comments;
         end = text.indexOf("@*/", lastIndex);
         if (lastIndex > -1)                       //Stop searching When End of File is reached
            lastIndex = end;
         else return comments;
         end = end - begin;
         System.out.println("Comment found: Begin: " + begin + " length: "
               + end);
         comments.add(new Comment(begin, end));
      }
      System.out.println(text.indexOf("/*@"));
      return comments;
   }
   /**
    * isInJMLcomment checks whether an offset position is inside a JML Multiline Comment Section
    * @param offset The offset to check whether it is in a JML Comment
    * @return true if offset is in JML Multiline Comment false if not
    */
   public boolean isInJMLcomment(int offset){
      LinkedList<Comment> comments = findCommentOffsets();
      int commentOffset;
      int commentLength;
         for(ListIterator<Comment> i=comments.listIterator(); i.hasNext(); i.next()){
            commentOffset=i.next().offset;
            commentLength=i.next().length;
               if(commentOffset<=offset&&commentLength+commentOffset>=offset)
                  return true;
      }
         return false;
   }
  
   /**
    * {@inheritDoc}
    */
   @Override
   public int getTabWidth(ISourceViewer sourceViewer, int currentResult) {
      this.document=sourceViewer.getDocument();//TODO is this Method called only once? 
      findCommentOffsets();
      return currentResult * 2;
   }

   @Override
   public IPresentationReconciler getPresentationReconciler(
         ISourceViewer sourceViewer, IPresentationReconciler currentResult) {
         return currentResult;
      }
   
   /**
    * @return extendedContentTypes A List of the previously defined
    *         ContentTypes, with JMLMultiLine content at first position in the
    *         array, and JMLSingleLine content on the second position followed
    *         by the previously defined content Types
    */
   @Override
   public String[] getConfiguredContentTypes(ISourceViewer sourceViewer,
         String[] currentResult) {
      if (currentResult[0].equals(JMLPartitionScanner.JML_MULTI_LINE)) //if Method was called
         return currentResult;                                         //previously there is
      else {                                                           // nothing to change
         String[] extendedContentTypes = new String[currentResult.length + 2];
         extendedContentTypes[0] = JMLPartitionScanner.JML_MULTI_LINE;
         extendedContentTypes[1] = JMLPartitionScanner.JML_SINGLE_LINE;
         for (int i = 0; i < currentResult.length; i++) {
            extendedContentTypes[i + 2] = currentResult[i];
         }
         return extendedContentTypes;
      }
   }
}
