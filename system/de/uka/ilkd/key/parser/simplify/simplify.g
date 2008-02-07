// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//


/* -*-antlr-*- */
header {

    package de.uka.ilkd.key.parser.simplify;

    import de.uka.ilkd.key.unittest.simplify.ast.*;
    import de.uka.ilkd.key.java.Services;
    import de.uka.ilkd.key.util.ExtList;
}


class SimplifyParser extends Parser;
options {
	importVocab=SimplifyLexer;
	k = 1;
	defaultErrorHandler=true;
}

{

    private Services services;

    public SimplifyParser(TokenStream lexer, Services services){
	    this(lexer);
        this.services = services;
    }

    public void reportError(RecognitionException ex){
        services.getExceptionHandler().reportException(ex);
    }


}

top returns[Conjunction result=null]
{
    Term f;
    ExtList l = new ExtList();
}: 
        LPAREN AND ( f=formula {l.add(f);})* RPAREN 
        {
            result = new Conjunction(l);
        }
    ;

formula returns[Term result=null]:
        result=literal 
    ;

literal returns[CompFormula result=null] 
{
    Term t;
}: 
        LPAREN 
        ( 
            EQ {result = new Equation();} 
        |   
            NEQ {result = new Inequation();}
        | 
            LT {result = new Less();}
        | 
            LEQ {result = new LessEq();}
        ) 
        t=term {result.setLeft(t);} 
        t=term {result.setRight(t);} 
        RPAREN
;   

term returns[Term t=null]
{
    ExtList l = new ExtList();
    int i;
    Term sub;
    Function f;
}: 
        f=attr {t=new FunctionTerm(f);}
    |
        f=func {t=new FunctionTerm(f);}
    |
        i=integer {t=new NumberTerm(i);} 
    | 
        LPAREN 
        (
            f=func (sub=term {l.add(sub);})*
            {
                t = new FunctionTerm(f, l); 
            }
        |
            PLUS (sub=term {l.add(sub);})+
            {
                t = new Plus(l); 
            }
        |
            MINUS (sub=term {l.add(sub);})+
            {
                t = new Minus(l);
            }
        |
            MUL (sub=term {l.add(sub);})+ 
            {
                t = new Mul(l); 
            }
        )
        RPAREN       
    ;

func returns[Function f = null]:
        id:IDENT 
        {
            if(id.getText().startsWith("length")){
                f = new ArrayLength(id.getText());
            }else{
                f = new Function(id.getText());
            }
        }
    |
        f=attr
    ;

attr returns[Function f = null]
{
    boolean dot=false;
    String className;
//    Token id, id1, id2;
}:
        BAR 
        (DOT {dot=true;})? 
        id1:IDENT {className = id1.getText();} 
        ( 
            DOT id3:IDENT 
            {
                className += "."+id3.getText();
            }
        )* 
        (
            COLON COLON 
            id2:IDENT
        )?
        BAR
        {
            if(id2!=null){
                if(dot){
                    f = new AttributeOp(className, id2.getText());
                }else{
                    f = new StaticAttr(className, id2.getText());
                }
            }else if(className.startsWith("length")){
                f = new ArrayLength(className);
            }else if(id1!=null){
                f = new Function(id1.getText());
            }
        }
    ;

integer returns[int i=0]
{
    boolean neg = false;
}:
        (MINUS {neg = true;})? d:DIGITS
        {
            i = Integer.parseInt((neg ? "-" : "")+d.getText());
        }
    ;
