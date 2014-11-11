package org.key_project.javaeditor.extension;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.ITokenScanner;

public class SingleTokenScanner implements ITokenScanner {

   public SingleTokenScanner(TextAttribute textAttribute) {
      // TODO Auto-generated constructor stub
   }

   @Override
   public void setRange(IDocument document, int offset, int length) {
      // TODO Auto-generated method stub
      
   }

   @Override
   public IToken nextToken() {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public int getTokenOffset() {
      // TODO Auto-generated method stub
      return 0;
   }

   @Override
   public int getTokenLength() {
      // TODO Auto-generated method stub
      return 0;
   }

}
