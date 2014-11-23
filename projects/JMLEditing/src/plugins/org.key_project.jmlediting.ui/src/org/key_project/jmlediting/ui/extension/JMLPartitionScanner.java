package org.key_project.jmlediting.ui.extension;

import org.eclipse.jdt.internal.ui.text.FastJavaPartitionScanner;
import org.eclipse.jdt.internal.ui.text.JavaPartitionScanner;
import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.Token;

import java.util.ArrayList;
import java.util.List;

public class JMLPartitionScanner extends RuleBasedPartitionScanner {
   
   /**
    * Identifier for JML MultiLine Code.
    */
   public static final String JML_MULTI_LINE = "__jml_multi_line";
   
   /**
    * Identifier for JML Single Line Code.
    */
   public static final String JML_SINGLE_LINE = "__jml_single_line";
   
   /**
    * Creates a JMLPartitionScanner that Detects SingleLine and MultiLine JML Code.
    */
   @SuppressWarnings({ })
   public JMLPartitionScanner() {
      super();
       
      IToken singleLineJML = new Token(JML_SINGLE_LINE);
      IToken multiLineJML = new Token(JML_MULTI_LINE);
      IPredicateRule[] rules =new IPredicateRule[fRules.length+2];
        
      rules[0]=new EndOfLineRule("//@", singleLineJML);
      rules[1]=new MultiLineRule("/*@", "@*/", multiLineJML);
      for(int i=0;i<fRules.length;i++)
         rules[i+2]=(IPredicateRule)fRules[i];
      setPredicateRules(rules);
      
      
      
   }
   

}
