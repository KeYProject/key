// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.parser;

import org.antlr.runtime.LegacyCommonTokenStream;

import antlr.TokenStreamSelector;

public class DeclPicker extends LegacyCommonTokenStream {
  private String text = null;
  private int lastMark = 0;

  /** Stream to read tokens from */
  public DeclPicker(KeYLexerF in) {
      super(in.getKeYLexer());
  }

  public int begin() {
     // see super.mark() implementation
     if (super.index() == -1) {
	 super.fillBuffer();
     }
     lastMark = super.index();
     return lastMark;
  }
  
  public void capture() {
     text = this.toString(lastMark, super.index() - 1);
  }
  
  public String getCapturedText() {
      return text;
  }

    /**
     * @return <code>null</code>
     * @deprecated
     */
    public TokenStreamSelector getSelector() {
	return null;
    }
  




  /** This makes us a stream 
  public Token nextToken() throws antlr.TokenStreamException {
    t = input.nextToken();
    if (finished) return t;
    
    if (t.getType() == KeYLexerTokenTypes.SORTS ||
        t.getType() == KeYLexerTokenTypes.FUNCTIONS ||
        t.getType() == KeYLexerTokenTypes.PREDICATES ||
        t.getType() == KeYLexerTokenTypes.SCHEMA ||
        t.getType() == KeYLexerTokenTypes.RULES ||
        t.getType() == KeYLexerTokenTypes.HEURISTICS) {
//       System.out.println("\n"); 
       copyState = true;
       input.mark();
    }

    if (t.getType() == KeYLexerTokenTypes.PROBLEM) {
       copyState = false;
       finished = true;
System.err.println(       input.getInputBuffer().getMarkedChars());
    }
    
    
//    if (copyState) {
//       System.out.print(t.getText());
//       if (t.getType() == KeYLexerTokenTypes.SEMI)
//         System.out.println();
//       else
//          System.out.print(" ");
//    }
    
    return t;
  }
*/  
  
  
}
