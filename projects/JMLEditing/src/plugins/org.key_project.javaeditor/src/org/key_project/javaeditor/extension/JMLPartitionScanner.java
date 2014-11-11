package org.key_project.javaeditor.extension;

import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.Token;

import java.util.ArrayList;
import java.util.List;

public class JMLPartitionScanner extends RuleBasedPartitionScanner{
   
   /**
    * Identifier for JML Multi Line Code
    */
   static final String JMLMultiLine = "JML_MULTI_LINE";
   
   /**
    * Identifier for JML Single Line Code
    */
   static final String JMLSingleLine = "JML_SINGLE_LINE";
   
   @SuppressWarnings({ "rawtypes", "unchecked" })
   public JMLPartitionScanner(){
      super();
      IToken singleLineJML = new Token(JMLSingleLine);
      IToken multiLineJML = new Token(JMLMultiLine);
      
      List rules = new ArrayList();
      
      rules.add(new EndOfLineRule("//@", singleLineJML));
      rules.add(new MultiLineRule("/*@", "@*/", multiLineJML));
      IPredicateRule[] result = new IPredicateRule[rules.size()];
      rules.toArray(result);
      setPredicateRules(result);
      
      
      
   }
   

}
