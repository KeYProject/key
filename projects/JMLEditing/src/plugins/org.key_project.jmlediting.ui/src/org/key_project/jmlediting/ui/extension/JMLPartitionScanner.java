package org.key_project.jmlediting.ui.extension;

import org.eclipse.jdt.internal.ui.text.JavaPartitionScanner;
import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.Token;

@SuppressWarnings("restriction")
public class JMLPartitionScanner extends JavaPartitionScanner {
   
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
   @SuppressWarnings({ "rawtypes", "unchecked" })
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
   public static String [] getLegalContentTypes(){
      return new String[]{JavaPartitionScanner.JAVA_CHARACTER,JavaPartitionScanner.JAVA_DOC, JavaPartitionScanner.JAVA_MULTI_LINE_COMMENT,
            JavaPartitionScanner.JAVA_SINGLE_LINE_COMMENT, JavaPartitionScanner.JAVA_STRING, JMLPartitionScanner.JML_MULTI_LINE, JMLPartitionScanner.JML_SINGLE_LINE};
      }
}
