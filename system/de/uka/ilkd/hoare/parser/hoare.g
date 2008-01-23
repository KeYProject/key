// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/* -*-antlr-*- */
header {
package de.uka.ilkd.hoare.parser;
import antlr.*;
import java.io.*;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
}

/** 
 * A simple program parser to check syntactical correctness of a Hoare logic program
 */  
class KeYHoareParser extends Parser;
options {
    importVocab=KeYHoareLexer;
    k = 1;
    defaultErrorHandler=false;
}

{
    private final static int NONE = -1; 
    private final static int BOOLEAN = 0; 
    private final static int INT = 1; 
    
    private Namespace pvs;
    
    private int lineOffset;
   
    
    public KeYHoareParser(KeYHoareLexer khl, Namespace pvs, int lineOffset) {
        this(khl);       
        this.pvs = pvs;
        this.lineOffset = lineOffset;   	
        
    }
    
    public int resolveLocationType(String id) {
        int type = NONE;
        ProgramVariable pv = (ProgramVariable)pvs.lookup(new Name(id));
        if (pv == null) {
            reportError("Programvariable " + pv + " not declared.");
        } 
        if (pv.sort().name().toString().equals("boolean")) {
            type = BOOLEAN;
        } else if (pv.sort().name().toString().equals("jint")) {
            type = INT;
        } else {
            reportError("Programvariable " + pv + " of unknown type " + pv.sort());
        }
        return type;
    }
    
    private int getLine() {
        int line = -1;
        try {
            line = LT(0).getLine();
        } catch (TokenStreamException e) {
            System.err.println("No further token in stream");
        }        
        return line + lineOffset;
    }   

    private int getColumn() {
        int col = -1;
        try {
            col = LT(0).getColumn();
        } catch (TokenStreamException e) {
            System.err.println("No further token in stream");
        }
        return col;
    }   
      
    public void reportError(String s, int line, int column) throws antlr.SemanticException {
        throw new antlr.SemanticException(s, getFilename(), line+lineOffset, column);
    }
    
    public static void main(String[] args) throws Throwable {
        KeYHoareLexer lexer = new KeYHoareLexer(new FileReader(args[0]));
		lexer.setFilename(args[0]);

        // Create a parser that reads from the scanner
		KeYHoareParser parser = new KeYHoareParser(lexer);
		parser.setFilename(args[0]);
		// start parsing at the compilationUnit rule
		parser.program();
    }
}

program 
{} :
        (statement)?
    ;exception
        catch [NoViableAltException ex] {
              throw new RecognitionException(ex.getMessage(), getFilename(), getLine(), getColumn());
        }

statement
{} :
        (SEMI      | 
            assignmentStatement |
            conditionalStatement |
            loopStatement )+
    ;


assignmentStatement 
{
    String l = null;
    int type = NONE;
} :
        l=location ASSIGN type=expression SEMI
        { if (resolveLocationType(l) != type) {
       	      reportError("Incompatible types in assignment.", getLine(), getColumn());
          }
        }
    ;


conditionalStatement
{
    int type = NONE;
}:
        IF LPAREN type=expression {
          if (type!=BOOLEAN) {
             reportError("Condition must be of boolean type", getLine(), getColumn());
          } 
        } RPAREN LBRACE
          (statement)?
        RBRACE 
        ELSE LBRACE 
          (statement)?
        RBRACE
    ;

loopStatement 
{
    int type = NONE;
}:
        WHILE LPAREN type=expression {
          if (type!=BOOLEAN) {
             reportError("Condition must be of boolean type", getLine(), getColumn());
          } }
        RPAREN LBRACE
           (statement)?
        RBRACE
    ;  

expression returns [int type = NONE]
{} :
        type = orExpression
    ;

orExpression returns [int type = NONE]
{
    int rightType = NONE;
} :
        type=andExpression (op:OR rightType=andExpression 
            {    if (type != BOOLEAN || rightType != BOOLEAN) {
                    reportError("In an or-expression both arguments must be of type boolean.", 
                                getLine(), getColumn()); 
                }
            }
        )* 
    ;

andExpression returns [int type = NONE]
{
    int rightType = NONE;
} :
        type=notExpression (op:AND rightType=notExpression
            {    
                if (type != BOOLEAN || rightType != BOOLEAN) {
                    reportError("In an and-expression both arguments must be of type boolean.", 
                                getLine(), getColumn()); 
                } 
            }  	
        )*
    ;

notExpression returns [int type = NONE]
{
    int rightType = NONE;
} :
        op:NOT type=notExpression {
            if (type != BOOLEAN) {
                reportError("Only boolean values can be negated.", 
                            getLine(), getColumn()); 
            } 		
        }
    | type=equalityExpression 
        
    ;

equalityExpression returns [int type = NONE]
{
    int rightType = NONE;
} :
      type=comparisonExpression (op:EQUALS rightType=comparisonExpression {
            if (type != rightType) {
                reportError("The comparison "+ op.getText() +" requires attributes of same type.", 
                            getLine(), getColumn());
            } else {
                type = BOOLEAN;
            }
        }
     )*
;

comparisonExpression returns [int type = NONE]
{
    Token op = null;
    int rightType = NONE;
}:
        type=intExpression (op=comparisonOperator rightType=intExpression {
                if (type != rightType || rightType == BOOLEAN) {
                    reportError("The comparison "+ op.getText() +" requires arguments of type int.", 
                        getLine(), getColumn());
                } else {
            type = BOOLEAN;
        }
    })? 
;


comparisonOperator returns [Token t = null]
{} :
        lt:LT { t = lt; } | leq:LEQ { t = leq; }| geq:GEQ { t = geq; }| gt:GT { t = gt; }
    ;

intExpression returns [int type = NONE]
{
    int rightType = NONE;
} :
        type=weakIntExpression
    ;

weakIntExpression returns [int type = NONE]
{
    Token op = null;
    int rightType = NONE;
} :
        type=strongIntExpression (op=weakOp rightType=strongIntExpression {
                if (type==INT && rightType==INT) {
                    type = INT;
                } else {
            reportError("The arithmetic operator " + op + " requires int typed arguments.", 
                getLine(), getColumn());
        }    
    }
    )* 
;


strongIntExpression returns [int type = NONE]
{
    Token op = null;
    int rightType = NONE;
} :
        type=atomicExpression (op=strongOp rightType=atomicExpression { 
                if (type==INT && rightType==INT) {
                    type = INT;
                } else {
            reportError("The arithmetic operator " + op + " requires int typed arguments.", 
                getLine(), getColumn());
        }
    }
    )* 
;


atomicExpression returns [int type = NONE]
{
    String id = null;
    int rightType = NONE;
} :
        NUM_LITERAL {type = INT;} | id=location {
            type = resolveLocationType(id);
        } |
        LPAREN type=expression RPAREN | TRUE {type = BOOLEAN;} | FALSE {type = BOOLEAN;} 
    ;

weakOp returns [Token t = null]
{} :
        plus:PLUS {t = plus;} | minus:MINUS {t=minus;}
    ;

strongOp returns [Token t = null]
{} :
        mul:MULT {t=mul;} | div:DIV {t=div;} | mod:MOD {t=mod;}
    ;

location returns [String t = null]
{} :
        id:IDENT {t=id.getText();}
    ;
