package org.key_project.jmlediting.core.editor;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.BufferedRuleBasedScanner;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.ITokenScanner;
import org.eclipse.jface.text.rules.Token;

public class SingleTokenScanner extends BufferedRuleBasedScanner {

   public SingleTokenScanner(TextAttribute textAttribute) {
      // TODO Auto-generated constructor stub
      setDefaultReturnToken(new Token(textAttribute));
   }
}
