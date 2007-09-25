// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

header {

    package de.uka.ilkd.asmkey.parser.antlr;

    import de.uka.ilkd.asmkey.parser.*;
    import de.uka.ilkd.asmkey.parser.ast.*;
    import de.uka.ilkd.key.parser.Location;
    import de.uka.ilkd.asmkey.logic.AsmOperator;
    import de.uka.ilkd.asmkey.logic.dfinfo.*;

    import java.util.*;

}


class AsmKeyParser extends Parser;


options {
	importVocab = AsmKeyLexer;
	k = 2;
	defaultErrorHandler = false;
    //codeGenMakeSwitchThreshold = 2;  // Some optimizations
	//codeGenBitsetTestThreshold = 3;
}


{

    /* --- static methods --- */

    private static final Location getLocation(AstDeclaration[] decls) {
        if (decls.length == 0) {
            return null;
        } else {
            return decls[0].getLocation();
        }
    }

    private static final Location getLocation(AstTerm[] terms) {
        if (terms.length == 0) {
            return null;
        } else {
            return terms[0].getLocation();
        }
    }

    /** Return a new empty list. */
    private static List createList() {
        return new ArrayList();
    }

    /** return a new array 't # terms'. */
    private static AstTerm[] prependTerm(AstTerm t, AstTerm[] terms) {
        AstTerm[] a = new AstTerm[terms.length + 1];
        System.arraycopy(terms, 0, a, 1, terms.length);
        a[0] = t;
        return a;
    }
    
    /** to create term with n-arry operators */
    private AstTerm createNarryTerm(Location l, AstTerm[] ts, Location opTokenLoc, Operator op) {
        return af.createTerm(l, new AstOperator(opTokenLoc, op), ts);
    }

    private AstTerm createIfTerm(AstTerm t1, AstTerm t2, AstTerm t3, Token opToken, Operator op) {
        Location loc=createLocation(opToken);
        return createNarryTerm(loc, new AstTerm[]{ t1,t2,t3 }, loc, op);
    }

    /** to creates term with binary operators */
    private AstTerm createBinaryTerm(AstTerm t1, AstTerm t2, Token opToken, Operator op) {
        return createNarryTerm(t1.getLocation(), new AstTerm[]{ t1, t2 }, createLocation(opToken), op);
    }

    /** to create terms with unary operator */
    private AstTerm createUnaryTerm(AstTerm t, Token opToken, Operator op) {
        return createNarryTerm(t.getLocation(), new AstTerm[] {t}, createLocation(opToken), op);
    }

    /** to create terms with nullary operator */
    private AstTerm createNullaryTerm(Token opToken, Operator op) {
        Location l = createLocation(opToken);
        return createNarryTerm(l, new AstTerm[0], l, op);
    }

    /** to create AstRestrictedSymbol[] from Identifier[] */
    private AstRestrictedSymbol[] createAstRestrictedSymbols(int type, Identifier[] ids) {
        AstRestrictedSymbol[] symbs = new AstRestrictedSymbol[ids.length];
        for (int i=0; i<ids.length; i++) {
            symbs[i] = new AstRestrictedSymbol(ids[i].getLocation(), type, ids[i]);
        }
        return symbs;
    }

    /* --- static fields --- */

    private static final AstTerm[] EMPTY_TERMS = new AstTerm[]{ };

    private static final Identifier[] EMPTY_IDS = new Identifier[]{ };
    
    private static final AstCondition[] EMPTY_CONDITIONS = new AstCondition[]{ };

    private static final AstParameter[] EMPTY_PARAMETERS = new AstParameter[]{ };
    
    private static final AstType[] EMPTY_TYPES = new AstType[]{ };

    private static final AstSchemaType[] EMPTY_SCHEMATYPES = new AstSchemaType[]{ };

    
    /* --- constructors --- */

    /** Create a parser with the given input and the given ast factory. */
    public AsmKeyParser(AsmKeyLexer lexer, AstFactory af) {
        this(lexer);
        this.af = af;
        this.filename = lexer.getFilename();
    }


    /* --- fields --- */

    /** The used AstFactory. */
    private AstFactory af = null;

    private String filename;

    /* --- methods --- */

    public String getFilename() {
        return filename;
    }

    
    private final Location createLocation(Token token) {
        return new Location(this.filename, token.getLine(), token.getColumn());
    }

    /* --- inner class --- */

    /** This class stores either a term or a sequent. It is needed
     * because some productions can't distinguish between terms and 
     * sequents without infinte lookahead.  */
    private static final class TermSequent {
        
        final AstTerm term;
        
        final AstSequent sequent;


        TermSequent(AstTerm term) {
            this(term, null);
        }

        TermSequent(AstSequent sequent) {
            this(null, sequent);
        }

        TermSequent(AstTerm term, AstSequent sequent) {
            this.term = term;
            this.sequent = sequent;
        }

    }
    
}

/* top declarations reading finite files and string with EOF. */

top_formula returns [AstTerm t]
    :
        t=term EOF
    ;

top_term returns [AstTerm t]
    :
        t=term EOF
    ;

top_asm_rule returns [AstAsmRule r]
    :
        r=asmRule EOF
    ;

top_unit returns [AstUnit u]
    :
        u=unit EOF
    ;

top_proof returns [AstProof p]
    :
        p=proof EOF
    ;

/* top declarations for tests */

top_ident returns [Identifier i]
    :
        i=ident EOF
    ;

top_bigident returns [Identifier i]
    :
        i=bigident EOF
    ;

top_stepident returns [Identifier i]
    :
        i=stepident EOF
    ;

top_sortDeclaration returns [AstDeclaration d]
    :
        d=sortDecl EOF
    ;

top_schemaDeclaration returns [AstDeclaration[] d]
    :
        d=schemaVarDecl EOF
    ;

top_predicateDeclaration returns [AstDeclaration d]
    :
        d=predicateDecl EOF
    ;

top_functionDeclaration returns [AstDeclaration d]
    :
        d=functionDecl EOF
    ;

/* usual atomic constructs */

protected
quantifier returns [AstQuantifier q]
    :
        all:FORALL
        {
            q = new AstQuantifier(createLocation(all), Quantifier.ALL);
        }
    |
        ex:EXISTS
        {
            q = new AstQuantifier(createLocation(ex), Quantifier.EX);
        }
    ;

protected
ident returns [Identifier s]
	:
        id:IDENT
        {
			s = new Identifier(createLocation(id), id.getText());
		}
	;

protected
singleident returns [Identifier s]
    :
        s=ident
    ;

protected
ident_asm_rule returns [Identifier s]
    :
        (
            (s=ident)
        |
            (
                asm:ASM RULE
                {
                    s = new Identifier(createLocation(asm), "asm-rule");
                }
            )
        )
    ;
        
protected
bigident returns [Identifier s]
    :
        id:BIGIDENT 
        { 
            s = new Identifier(createLocation(id), id.getText());
        }
    ;

protected
stepident returns [Identifier s]
    :
        id:STEPIDENT
        {
            s = new Identifier(createLocation(id), id.getText());
        }
    ;

protected
identnarity returns [Identifier s]
    :
        id:IDENTNARITY
        {
            s = new Identifier(createLocation(id), id.getText());
        }
    ;

protected
identList returns [Identifier[] ids]
{
    Identifier id;
    List list = createList();
}
    :
        id=ident
        {
            list.add(id);
        }
        (
            COMMA id=ident
            {
                list.add(id);
            }
        )*
        {
            ids = (Identifier[]) list.toArray(new Identifier[list.size()]);
        }
    ;

protected
id_asm_rule_list returns [Identifier[] ids]
{
    Identifier id;
    List list = createList();
}
    :
       id=ident_asm_rule
        {
            list.add(id);
        }
        (
            COMMA id=ident_asm_rule
            {
                list.add(id);
            }
        )*
        {
            ids = (Identifier[]) list.toArray(new Identifier[list.size()]);
        } 
    ;

protected
identBarList returns [Identifier[] ids]
{
    Identifier id;
    List list = createList();
}
    :
        id=ident
        {
            list.add(id);
        }
        (
            OR id=ident
            {
                list.add(id);
            }
        )*
        {
            ids = (Identifier[]) list.toArray(new Identifier[list.size()]);
        }
    ;


/* Parsing of terms, formulas and sequent */


/**
 * In the special but important case of Taclets, we don't yet know
 * whether we are going to have a term or a formula, and it is hard
 * to decide a priori what we are looking at.  So the `term'
 * non-terminal will recognize a term or a formula.  The `formula'
 * reads a formula/term and throws an error if it wasn't a formula.
 * This gives a rather late error message. */
protected
formula returns [AstTerm t]
    :
        t=term
    ;


/**
 * Terms and formulas: the precedence for usual boolean and integral numbers 
 * is set as following (from weaker to to stronger)
 * -- formulas
 * (15) equivalent <->
 * (14) implies ->
 * (13) or |
 * (12) and &
 * (11) unary operators: not, [[]], <<>>, quantifiers
 * (10) equality of terms
 * -- terms
 * (9) or, or else
 * (8) and, andalso
 * (7) not; all, any (restricted quantifiers as boolean operations)
 * (6) equality (is boolean operation)
 * (5) addition, sustraction.
 * (4) multiplication, division.
 * // (3) sign, to see
 * (2) step information
 * (1) functions call, sequences (lists), numbers, abreviations, logical constants.
 */
protected
term returns [AstTerm t]
    :
        t=bigFormula
    ;

protected
trueTerm returns [AstTerm t]
    :
        t=ifTerm
    ;

protected
bigFormula returns [AstTerm t]
{
    boolean big=false;
    boolean and=false;
    Identifier func=null;
    Identifier sort=null;
    Identifier narity=null;
    AstTerm t2;
    Location l;
}
    :
        (
            ( l1:BIGAND {and = true;} | l2:BIGOR {and = false;} ) {big=true;}
            LPAREN sort=ident COLON func=ident LPAREN narity=ident RPAREN RPAREN
        )?
        t2 = eqvFormula
        {
            if (big) {
                if (and) {
                    l = createLocation(l1);
                    t = af.createBigTerm(l,
                        new AstOperator(l, Operator.BIGAND), sort,
                        func, narity, t2);
                } else {
                    l = createLocation(l2);
                    t = af.createBigTerm(l,
                        new AstOperator(l, Operator.BIGOR), sort,
                        func, narity, t2);
                }
            } else {
                t = t2;
            }
        }
    ;

protected
eqvFormula returns [AstTerm t1]
{
    AstTerm t2;
}
    :
        t1=impFormula
        (
            eqv:EQV t2=eqvFormula
            {
                t1 = createBinaryTerm(t1, t2, eqv, Operator.EQV);
            }
        )?
    ;


protected
impFormula returns [AstTerm t1]
{
    AstTerm t2;
}
    :
        t1=orFormula
        (
            imp:IMP t2=impFormula
            {
                t1 = createBinaryTerm(t1, t2, imp, Operator.IMP);
            }
        )?
    ;


protected
orFormula returns [AstTerm t1]
{
    AstTerm t2;
}
    :
        t1=andFormula
        (
            or:OR t2=orFormula
            {
                t1 = createBinaryTerm(t1, t2, or, Operator.OR);
            }
        )?
    ;


protected
andFormula returns [AstTerm t1]
{
    AstTerm t2;
}
    :
        t1=unaryLogicalOpTerm
        (
            and:AND t2=andFormula
            {
                t1 = createBinaryTerm(t1, t2, and, Operator.AND);
            }
        )?
    ;

protected
unaryLogicalOpTerm returns [AstTerm t1]
{
    AstAsmRule r;
    AstTerm t2 = null;
    AstQuantifier q;
    Identifier var;
    Identifier sort = null;
    boolean waryEx = false;
    boolean waryAll = true; // to revise ?? 
}
    :
        t1 = equalityFormula
    |
        not:NOT t1=unaryLogicalOpTerm
        {
            t1 = createUnaryTerm(t1, not, Operator.NOT);
        }
    |
        each:DLBRACK r=asmRule DRBRACK (LT t2=term GT)? t1=unaryLogicalOpTerm
        {
            t1 = af.createDlBox(createLocation(each), r, t1, t2);
        }
    |
        some:DLT r=asmRule DGT (LT t2=term GT)?  t1=unaryLogicalOpTerm
        {
            t1 = af.createDlDiamond(createLocation(some), r, t1, t2);
        }
    |
        q=quantifier (sort=ident (COLON)?)? (var=ident | var=identnarity)  SEMI t1=unaryLogicalOpTerm
        {
            t1 = af.createTerm(q.getLocation(), q, var, sort, t1);
        }
    |
        LBRACE var=ident ( COLON sort=ident )? t1=term
        ((WARYEX {waryEx = true;}) | (WARYALL {waryAll = true;}))? RBRACE t2=unaryLogicalOpTerm
        {
            t1 = af.createSubstitutionTerm(var.getLocation(), var, sort, t1, t2, waryEx, waryAll);
        }
    ;

protected
equalityFormula returns [AstTerm t1]
{
    AstTerm t2;
}
    :
        t1=trueTerm
        (equals:EQUALS t2=trueTerm
            {
                t1 = createBinaryTerm(t1, t2, equals, Operator.EQUALS);
            }
        )?
    ;

protected
ifTerm returns [AstTerm t1]
{
    AstTerm t2, t3;
}
    :
        (
            t1=orTerm
        |
            if_:IF t1=ifTerm ASMTHEN t2=ifTerm ASMELSE t3=ifTerm ASMEND (IF)?
            {
                t1=createIfTerm(t1, t2, t3, if_, Operator.TERM_IF);
            }
        )
    ;

protected
orTerm returns [AstTerm t1]
{
    AstTerm t2;
    Operator op;
    Token tok;
}
    :
        t1=andTerm
        (
            (
                orelse:ASMOR ASMELSE { op = Operator.TERM_ORELSE; tok = orelse;}
            |   or:ASMOR {op = Operator.TERM_OR; tok = or;}
            )
            t2=orTerm
            {
                t1 = createBinaryTerm(t1, t2, tok, op);
            }
        )?
    ;

protected
andTerm returns [AstTerm t1]
{
    AstTerm t2;
    Operator op;
    Token tok;
}
    :
        t1 = equalityTerm
        (
            (
                andalso:ASMAND ASMALSO { op = Operator.TERM_ANDALSO; tok = andalso;}
            |   and:ASMAND {op = Operator.TERM_AND; tok = and;}
            )
            t2=andTerm
            {
                t1 = createBinaryTerm(t1, t2, tok, op);
            }
        )?
    ;

protected
equalityTerm returns [AstTerm t1]
{
    AstTerm t2;
}
    :
        t1=additiveTerm
        (
            equals:TERMEQUALS t2=equalityTerm
            {
                t1 = createBinaryTerm(t1, t2, equals, Operator.TERM_EQUALS);
            }
        )?
    ;

protected
additiveTerm returns [AstTerm t1]
{
    AstTerm t2;
}
    :
        t1=multiplicativeTerm
        (
            (
                plus:PLUS t2=additiveTerm
                {
                    t1 = createBinaryTerm(t1, t2, plus, Operator.ADD);
                }
            )
        |
            (
                minus:MINUS t2=additiveTerm
                {
                    t1 = createBinaryTerm(t1, t2, minus, Operator.SUB);
                }
            )
        )?
    ;


protected
multiplicativeTerm returns [AstTerm t1]
{
    AstTerm t2;
}
    :
        t1=stepTerm
        (
            (
                asterix:ASTERIX t2=multiplicativeTerm
                {
                    t1 = createBinaryTerm(t1, t2, asterix, Operator.MULT);
                }
            )
        |
            (
                slash:SLASH t2=multiplicativeTerm
                {
                    t1 = createBinaryTerm(t1, t2, slash, Operator.DIV);
                }
            )
        )?
    ;




protected
stepTerm returns [AstTerm t1]
{
    AstTerm t2;
}
    :
        t1=atomicTerm
        (
            step:LT t2=additiveTerm GT
            {
                t1 = createBinaryTerm(t1, t2, step, Operator.STEP);
            }
        )?
    ;

protected
atomicTerm returns [AstTerm t]
{
    Location location;
    Identifier abbr;
    AstTerm t1;
}
    :
        (
            t=funcPredVarTerm
        |
            t=sequenceTerm
        |
            LPAREN t=term RPAREN
        |
            true_:TRUE
            {
                t = createNullaryTerm(true_, Operator.TRUE);
            }
        |
            false_:FALSE
            {
                t = createNullaryTerm(false_, Operator.FALSE);
            } 
        |
            at:AT abbr=ident
            {
                t = af.createAbbreviationTerm(createLocation(at), abbr);
            }
        )
    ;



protected
funcPredVarTerm returns [AstTerm a]
{
    Identifier id;
    AstTerm[] l=null;
    AstTerm t=null;
}
    :
        (
            id=ident (l=termArgs)?
        |
            id=stepident LT t=additiveTerm GT (l=termArgs)?
        |
            id=identnarity
        )
        {
            if (l==null) {
                l=EMPTY_TERMS;
            }
            if (t != null) {
                AstTerm[] temp;
                int k = l.length;
                temp = new AstTerm[k + 1];
                for (int i=1; i<= k; i++) {
                    temp[i] = l[i-1];
                }
                temp[0] = t;
                l = temp;
            }
            a = af.createTerm(id.getLocation(), id, l);
        }
    ;

protected
termArgs returns [AstTerm[] terms]
{
    Identifier id;
    AstTerm[] rules=null;
}
    :
        LPAREN (COLON rules=asmRuleList SEMI)?
        (
            terms=termList RPAREN
            {
                if (rules !=null) {
                    AstTerm[] olds = terms;
                    terms = new AstTerm[olds.length + rules.length];
                    for(int i =0; i<rules.length; i++) { terms[i] = rules[i]; }
                    for(int i=rules.length;i<terms.length;i++) { terms[i] = olds[i-rules.length]; }
                }
            }
        |
            RPAREN
            {
                terms = rules==null?EMPTY_TERMS:rules;
            }
        )
    ;

protected
sequenceTerm returns [AstTerm t]
{
    AstTerm[] elems = null;
    AstTerm tail = null;
    Identifier basesort = null; 
}
    :
        lbrack:LBRACK
        (basesort=ident COLON)?
        (elems=trueTermList)?
        (OR tail=trueTerm)? // OR is used as a bar, cf. prolog lists
        {
            t = af.createSequenceTerm(createLocation(lbrack), basesort, elems, tail);
        }
        RBRACK
    ;

protected
termList returns [AstTerm[] terms]
{
    List list = createList();
    AstTerm t;
}
    :
        t=term
        {
            list.add(t);
        }
        (
            COMMA t=term
            {
                list.add(t);
            }
        )*
        { 
            terms = (AstTerm[]) list.toArray(new AstTerm[list.size()]);
        }
    ;

protected
trueTermList returns [AstTerm[] terms]
{
    List list = createList();
    AstTerm t;
}
    :
        t=trueTerm
        {
            list.add(t);
        }
        (
            COMMA t=trueTerm
            {
                list.add(t);
            }
        )*
        { 
            terms = (AstTerm[]) list.toArray(new AstTerm[list.size()]);
        }
    ;

/* sequents */

/** parse a sequent */
protected
seq returns [AstSequent s]
{
    AstTerm[] ant = EMPTY_TERMS, suc = EMPTY_TERMS;
} 
    : 
        (
            ant=termList 
        )?
        SEQARROW
        (
            suc=termList
        )?
        { 
            s = new AstSequent(getLocation(ant), ant, suc);
        }
    ;


protected
termorseq returns [TermSequent ts]
{
    AstTerm t;
    AstTerm[] ant, suc = EMPTY_TERMS;
}
    :
        (
            t=term
            (
                /* empty */
                {
                    ts = new TermSequent(t);
                }
            |
                SEQARROW
                (
                    suc=termList
                )?
                {
                    ts = new TermSequent(new AstSequent(t.getLocation(), new AstTerm[]{ t }, suc));
                }
            |
                COMMA ant=termList SEQARROW
                (
                    suc=termList
                )?
                {
                    ts = new TermSequent(new AstSequent(t.getLocation(), prependTerm(t, ant), suc));
                }
            )
        |
            seqarrow:SEQARROW 
            (
                suc=termList
            )?
            {
                ts = new TermSequent(new AstSequent(createLocation(seqarrow), EMPTY_TERMS, suc));
            }
        )
    ;


/* asm rules */

/** 
 * the asm rules binary operators are given the following precendence
 * from weaker to stronger:
 * (3) seq
 * (2) par
 * (1) rest
 */
protected
asmRule returns [AstAsmRule r]
    :
        r=seqAsm
    ;

protected
seqAsm returns [AstAsmRule r1]
{
    AstAsmRule r2;
}
    :
        r1=parAsm 
        ( 
            ASMSEQ r2=seqAsm 
            { 
                r1 = af.createAsmSeq(r1.getLocation(), r1, r2);
            }
        )?
    ;

protected
parAsm returns [AstAsmRule r1]
{
    AstAsmRule r2;
}
    :
        r1=atomicAsm 
        ( 
            ASMPAR r2=parAsm 
            {
                r1 = af.createAsmPar(r1.getLocation(), r1, r2);
            }
        )?
    ;

protected
atomicAsm returns [AstAsmRule r]
{
    Identifier id;
}
    :
        (
            r=skipAsm
        |
            r=assignAsm
        |
            r=ifAsm
        |
            r=condAsm
        |
            r=letAsm
        |
            r=forallAsm
        |
            r=tryAsm
        |
            r=substAsm
        |
            r=metaAsm
        |
            r=namedAsmCall
        |
            id=ident
            {
                r = af.createAsmVariable(id.getLocation(), id);
            }
        |
            LPAREN r=asmRule RPAREN
        )
    ;


protected
skipAsm returns [AstAsmRule r]
    :
        skip:ASMSKIP
        {
            r = af.createAsmSkip(createLocation(skip));
        }
    ;


protected
assignAsm returns [AstAsmRule r]
{
    AstTerm t1, t2;
}
    :
        t1=funcPredVarTerm ASSIGN t2=term
        {
            r = af.createAsmAssign(t1.getLocation(), t1, t2);
        }
    ;

protected
ifAsm returns [AstAsmRule r]
{
    AstTerm phi;
    AstAsmRule r1, r2=null;
}
    :
        if_:IF phi=formula ASMTHEN r1=asmRule
        (else_: ASMELSE r2=asmRule)?
        ASMEND (IF)?
        {
            r = af.createAsmIf(createLocation(if_), phi, r1, r2);
        }
    ;

protected
condAsm returns [AstAsmRule r]
{
    AstTerm phi;
    AstTerm[] phis;
    AstAsmRule[] rs;
    List phi_list = createList();
    List r_list = createList();
    r = null;
}
    :
        cond:ASMCOND
        (phi=term ASMTHEN r=asmRule ASMEND
            {phi_list.add(phi); r_list.add(r);})*
        {
            if (phi_list.size()==0) {
                phis = null; rs=null;
            } else {
                phis = ((AstTerm[])phi_list.toArray(new AstTerm[0]));
                rs = ((AstAsmRule[])r_list.toArray(new AstAsmRule[0]));
            }
        }
        (OTHERWISE r=asmRule ASMEND)?
        ASMEND (ASMCOND)?
        {
            r = af.createCondAsm(createLocation(cond), phis, rs, r);
        }
    ;

protected
letAsm returns [AstAsmRule r]
{
    Identifier v;
    Identifier sort = null;
    AstTerm t;
}
    :
        let:ASMLET (sort=ident COLON)? v=ident  EQUALS t=trueTerm
        ASMIN r=asmRule ASMEND (ASMLET)?
        {
            r = af.createAsmLet(createLocation(let), v, sort, t, r);
        }
    ;


protected
forallAsm returns [AstAsmRule r]
{
    Identifier v;
    Identifier sort = null;
    AstTerm t;
}
    :
        forall:ASMFORALL (sort=ident COLON)? v=ident  ASMWITH t=formula
        ASMDO r=asmRule ASMEND (ASMFORALL)?
        {
            r = af.createAsmForall(createLocation(forall), v, sort, t, r);
        }
    ;


protected
tryAsm returns [AstAsmRule r]
{
    AstAsmRule r1, r2;
}
    :
        try_:ASMTRY r1=asmRule ASMELSE r2=asmRule ASMEND (ASMTRY)?
        {
            r = af.createAsmTry(createLocation(try_), r1, r2);
        }
    ;

protected
namedAsmCall returns [AstAsmRule r]
{
    Identifier id;
    AstTerm[] l=null;
}
    :
        id=bigident (l=termArgs)?
        {
            r = af.createAsmCall(id.getLocation(), id, l);
        }
    ;


protected
substAsm returns [AstAsmRule r]
{
    Identifier var;
    Identifier sort = null;
    AstTerm t;
}
    :
        lbrace:LBRACE var=ident ( COLON sort=ident )? t=term RBRACE r=atomicAsm
        {
            r = af.createAsmSubstitution(createLocation(lbrace), var, sort, t, r);
        }
    ;


protected
metaAsm returns [AstAsmRule r]
{
    Identifier id;
}
    :
        at:AT id=ident LPAREN r=asmRule RPAREN
        {
            r = af.createAsmRuleMeta(createLocation(at), id, r);
        }
    ;

protected
asmRuleList returns [AstAsmRule[] rules]
{ 
    List list = createList();
    AstAsmRule r;
}
    :
        r=asmRule { list.add(r); }
        (
            COMMA r=asmRule { list.add(r); }
        )?
        {
            rules = ((AstAsmRule[]) list.toArray(new AstAsmRule[list.size()]));
        }
    ;


/* taclets */

/** 
 * this production recognize taclets
 */
protected
taclet returns [AstTaclet r]
{ 
    AstSequent s = null;
    TermSequent ts = null;
    AstCondition[] conds = EMPTY_CONDITIONS;
    AstGoal[] goals;
    AstTacletModifier[] mods;
    Location location = null;
    boolean sameUpdateLevel = false;
}
	: 
      ((
		( 
            if_:IF LPAREN s=seq RPAREN 
            {
                location = createLocation(if_);
            }
        )?
		( 
            find:FIND LPAREN ts=termorseq RPAREN 
            {
                if (location == null) {
                    location = createLocation(find);
                }
            }
        )?
        (
            ( VARCOND | COND ) LPAREN conds=conditions RPAREN
        )?
		goals=goalSpecs
        mods=modifiers
        {
            if (ts == null) {
                ts = new TermSequent(new AstSequent(null, EMPTY_TERMS, EMPTY_TERMS));
            }
            if (ts.term != null) {
                r = new AstTaclet(location, s, ts.term, conds, goals, mods);
            } else {
                r = new AstTaclet(location, s, ts.sequent, conds, goals, mods);
            }
        }
      ) |
        (builtin:BUILTIN 
                {
                    r = null;
                }
            ))
    ;


protected
conditions returns [AstCondition[] conds]
{
    AstCondition cond;
    List list = createList();
}
    :
        cond=condition
        {
            list.add(cond);
        }
        (
            COMMA cond=condition
            {
                list.add(cond);
            }
        )*
        {
            conds = (AstCondition[]) list.toArray(new AstCondition[list.size()]);
        }
    ;


protected
condition returns [AstCondition cond]
{
    Identifier v, w, r, f;
}
    :
        op:OP v=ident 
        (
            EQUALS w=ident
            {
                cond = af.createOperatorEqualsCondition(createLocation(op), true, v, w);
            }
        |
            NOTEQUALS w=ident
            
            {
                cond = af.createOperatorEqualsCondition(createLocation(op), false, v, w);
            }
        )
    |
        v=ident NOT  (
            FREE ASMIN w=ident
            {
                cond = af.createNotFreeCondition(v.getLocation(), v, w);
            }
        |
            UPDATE f=ident
            {
                cond = af.createNotUpdateCondition(v.getLocation(), v,f);
            }
        |
            ACCESS f=ident
            {
                cond = af.createNotAccessCondition(v.getLocation(), v, f);
            }
        )
    |
		v=ident NEW DEPENDING ON w=ident
        { 
            cond = af.createSkolemCondition(v.getLocation(), v, w);
        }
    |
        pure:PURE v=ident
        {
            cond = af.createPureCondition(createLocation(pure), v);
        }
    |
        static_:STATIC v=ident
        {
            cond = af.createStaticCondition(createLocation(static_), v);
        }
    |
        staticargs:STATICARGS v=ident
        {
            cond = af.createStaticArgsCondition(createLocation(staticargs), v);
        }
    |
        dynamic:DYNAMIC v=ident
        {
            cond = af.createDynamicCondition(createLocation(dynamic), v);
        }
    |
        atomic:ATOMIC v=ident
        {
            cond = af.createAtomicCondition(createLocation(atomic), v);
        }
    |
        call:DERIVED v=ident
        {
            cond = af.createDerivedCondition(createLocation(call), v);
        }
    |
        r=ident MAY  (
            UDPATE f=ident
            {
                cond = af.createMayUpdateCondition(r.getLocation(), r, f);
            }
        | 
            ACCESS f=ident
            {
                cond = af.createMayAccessCondition(r.getLocation(), r, f);
            }
        )
    ;


protected
goalSpecs returns [AstGoal[] goals]
    :
        CLOSE GOAL
        {
            goals = new AstGoal[]{ };
        }
    | 
        goals=goalSpecList
    ;


protected
goalSpecList returns [AstGoal[] goals]
{
    List list = createList();
    AstGoal g;
}
    :
        ((
            g=goalSpec
            {
                list.add(g);
            } 
            (
                SEMI g=goalSpec
                {
                    list.add(g);
                }
            )*
        )
        |
        (
            g=replaceBranch
            {
                list.add(g);
            }
        ))
        { 
            goals = (AstGoal[]) list.toArray(new AstGoal[list.size()]);
        }
    ;


protected
goalSpec returns [AstGoal goal] 
    :
        goal=replacewith
    ;


protected
replacewith returns [AstGoal goal]
{
    Location location = null;
    TermSequent ts = null;
    AstSequent s = null;
    AstTacletDeclaration[] l = null;
    String name = null;
}
    :
        (
            str:STRING_LITERAL COLON
            {
                name = str.getText();
            }
        )?
		(
            rw:REPLACEWITH 
            LPAREN ts=termorseq RPAREN
            {
                if (location == null) {
                    location = createLocation(rw);
                }
            }
        )?
        (
            add:ADD LPAREN s=seq RPAREN
            {
                if (location == null) {
                    location = createLocation(add);
                }
            }
        )?
        (
            addrules:ADDRULES LPAREN l=tacletDeclList RPAREN
            {
                if (location == null) {
                    location = createLocation(addrules);
                }
            }
        )?
        {
            if (ts == null) {
                goal = af.createReplaceGoal(location, name, (AstTerm) null, s, l);
            } else if (ts.term != null) {
                goal = af.createReplaceGoal(location, name, ts.term, s, l);
            } else {
                goal = af.createReplaceGoal(location, name, ts.sequent, s, l);
            }
        }
    ;

protected
replaceBranch returns [AstGoal g]
{
    AstSequent s;
}
    :
        replacebranch:REPLACEBRANCH
        LPAREN s=seq RPAREN
        {
            g = af.createReplaceGoal(createLocation(replacebranch), null, s);
        }
    ;

protected
tacletDeclList returns [AstTacletDeclaration[] l]
{
    AstTacletDeclaration decl;
    List list = createList();
}
    :
        decl=tacletDecl
        {
            list.add(decl);
        }
        (
            COMMA decl=tacletDecl
            {
                list.add(decl);
            }
        )*
        {
            l = (AstTacletDeclaration[]) list.toArray(new AstTacletDeclaration[list.size()]);
        }
    ;


protected
modifiers returns [AstTacletModifier[] l]
{
    List list = createList();
    AstTacletModifier tm;
}
    :
        (
            tm=modifier
            {
                list.add(tm);
            }
        )*
        {
            l = (AstTacletModifier[]) list.toArray(new AstTacletModifier[list.size()]);
        }
    ;


protected
modifier returns [AstTacletModifier tm]
{
    Identifier[] ids;
}
    :
        heurs:RULE SETS LPAREN ids=identList RPAREN
        {
            tm = af.createTacletHeuristics(createLocation(heurs), ids);
        }
    |
        ni:NONINTERACTIVE
        {
            tm = af.createTacletNonInteractiveModifier(createLocation(ni));
        }
    |
        dn:DISPLAYNAME dname:STRING_LITERAL
        {
            tm = af.createTacletDisplayNameModifier(createLocation(dn), dname.getText());
        }
    |
        ht:HELPTEXT htext:STRING_LITERAL
        {
            tm = af.createTacletHelpTextModifier(createLocation(ht), htext.getText());
            // b.setHelpText(htext.getText());
        }
    |
        ul:SAMEUDPATELEVEL
        {
            tm = af.createTacletSameUpdateLevelModifier(createLocation(ul));
        }
    |
        seqState:INSEQUENTSTATE
        {
            tm = af.createTacletInSequentStateModifier(createLocation(seqState));
        }

    ;



/* declarations */


/** we begin first by declaring type references
 * there is 2 kind of them:
 * (1) AstType: that comes as universes for the ASM.
 * (2) AstSchemaType: that comes as meta for the formation
 *     of predicates, taclets, parametrised lemmas (only formulas and rules), etc...
 */
 
protected
typeRef returns [AstType t]
{
    Identifier id;
}
    :
        LBRACK id=ident RBRACK {t=af.createSequenceTypeRef(id.getLocation(), id);}
    |
        id=ident {t=af.createPrimitiveTypeRef(id.getLocation(), id);}
    ;

protected
formulaOrTypeRef returns [AstType t]
    :
        
        t=typeRef
    |
        formula:FORMULA 
        {t= af.createSchemaTypeRef(createLocation(formula),
                PrimitiveSchemaType.FORMULA, false);}
    ;

protected
asmRuleTypeRef returns [AstType t]
    :
        asm:ASM RULE
        {t=af.createAsmRuleTypeRef(createLocation(asm));} 
    ;

protected
schemaTypeRef returns [AstSchemaType r]
{
    AstType sort;
    boolean variable = false;
    boolean depending = false;
    boolean static_ = false;
    boolean narity = false;
}
    :
        (
            asm:ASM RULE
            {
                r = af.createSchemaTypeRef(createLocation(asm), PrimitiveSchemaType.ASMRULE, false);
            }
        | 
            ( 
                VARIABLE 
                { 
                    variable = true; 
                }
            |
                DEPENDING
                {
                    depending = true;
                }
            |
                STATIC
                {
                    static_ = true;
                }
            )?
            (
                sort=typeRef 
                { 
                    if (depending) {
                        r = af.createDependingSchemaTypeRef(sort.getLocation(), sort);
                    } else if (variable) {
                        r = af.createVariableSchemaTypeRef(sort.getLocation(), sort);
                    } else {
                        r = af.createComposedSchemaTypeRef(sort.getLocation(), sort, static_);
                    }
                }
            |
                formula:FORMULA {!variable && !depending}?
                { 
                    r = af.createSchemaTypeRef(createLocation(formula),
                        PrimitiveSchemaType.FORMULA, static_);
                }	
            )
        )
    ;

/* different kind of arguments lists for declaring 
 * functions, predicates, dirived or not.
 */

protected
typeRefParameter returns [AstType p]
{
    Identifier id;
}
    :   
        p=typeRef ((COLON)? id=ident)?
    ;

protected
typeRefParameterList returns [AstType[] l]
{
    AstType p;
    List list = createList();
}
    :
        p=typeRefParameter
        {
            list.add(p);
        }
        (
            COMMA p=typeRefParameter
            {
                list.add(p);
            }
        )*
        {
            l = (AstType[]) list.toArray(new AstType[list.size()]);
        }
    ;


protected
typeRefParameters returns [AstType[] args = null]
    :
        (
            LPAREN
            (
                args = typeRefParameterList RPAREN
            |
                RPAREN
            )
        )?
        {
            if (args == null) {
                args = EMPTY_TYPES;
            }
        }
    ;

/* we have (obligatory) named parameters with simply type for
 * derived functions
 */

protected
typeRefNamedParameter returns [AstParameter p]
{
    Identifier id;
    AstType sort;
}
    :   
        sort=typeRef (COLON)? id=ident
        {
            p = new AstParameter(id.getLocation(), id, sort);
        }
    ;

protected
typeRefNamedParameterList returns [AstParameter[] l]
{
    AstParameter p;
    List list = createList();
}
    :
        p=typeRefNamedParameter
        {
            list.add(p);
        }
        (
            COMMA p=typeRefNamedParameter
            {
                list.add(p);
            }
        )*
        {
            l = (AstParameter[]) list.toArray(new AstParameter[list.size()]);
        }
    ;


protected
typeRefNamedParameters returns [AstParameter[] args = null]
    :
        (
            LPAREN
            (
                args = typeRefNamedParameterList RPAREN
            |
                RPAREN
            )
        )?
        { 
            if (args == null) {
                args = EMPTY_PARAMETERS;
            }
        }
    ;

/* now parameters for basic predicates */


protected
formulaOrTypeRefParameter returns [AstType p]
{
    Identifier id;
}
    :   
        p=formulaOrTypeRef ((COLON)? id=ident)?
    ;

protected
asmRuleTypeRefParameter returns [AstType p]
{
    Identifier id;
}
    :
        p=asmRuleTypeRef ((COLON)? id=ident)?
    ;

protected
formulaOrTypeRefParameterList returns [AstType[] l]
{
    AstType p;
    List list = createList();
}
    :
        p=formulaOrTypeRefParameter
        {
            list.add(p);
        }
        (
            COMMA p=formulaOrTypeRefParameter
            {
                list.add(p);
            }
        )*
        {
            l = (AstType[]) list.toArray(new AstType[list.size()]);
        }
    ;

protected
asmRuleTypeRefParameterList returns [AstType[] l]
{
    AstType p;
    List list = createList();
}
    :
        p=asmRuleTypeRefParameter {list.add(p);}
        (COMMA p=asmRuleTypeRefParameter {list.add(p);})*
        {
            l = (AstType[]) list.toArray(new AstType[list.size()]);
        }
    ;


protected
predicateParameters returns [AstType[] args = null]
{
    AstType[] rules=null;
}
    :
        (
            LPAREN (COLON rules = asmRuleTypeRefParameterList SEMI)?
            (
                args = formulaOrTypeRefParameterList RPAREN
                {
                    if (rules != null) {
                        AstType[] olds=args;
                        args=new AstType[olds.length + rules.length];
                        for(int i=0;i<rules.length;i++) { args[i] = rules[i]; }
                        for(int i=rules.length; i<args.length; i++)
                        {args[i] = olds[i-rules.length];}
                    }
                }
            |
                RPAREN    
            )
        )?
        {
            if (args == null) { 
                    args = rules==null?EMPTY_TYPES:rules;
            }
        }
    ;

/* parameters for derived predicates */

protected
formulaOrTypeRefNamedParameter returns [AstParameter p]
{
    Identifier id;
    AstType sort;
}
    :   
        sort=formulaOrTypeRef (COLON)? id=ident
        {
            p = new AstParameter(id.getLocation(), id, sort);
        }
    ;

protected
asmRuleTypeRefNamedParameter returns [AstParameter p]
{
    Identifier id;
    AstType sort;
}
    :
        sort=asmRuleTypeRef (COLON)? id=ident
        {
            p = new AstParameter(id.getLocation(), id, sort);
        }
    ;

protected
formulaOrTypeRefNamedParameterList returns [AstParameter[] l]
{
    AstParameter p;
    List list = createList();
}
    :
        p=formulaOrTypeRefNamedParameter
        {
            list.add(p);
        }
        (
            COMMA p=formulaOrTypeRefNamedParameter
            {
                list.add(p);
            }
        )*
        {
            l = (AstParameter[]) list.toArray(new AstParameter[list.size()]);
        }
    ;

protected
asmRuleTypeRefNamedParameterList returns [AstParameter[] l]
{
    AstParameter p;
    List list = createList();
}
    :
        p=asmRuleTypeRefNamedParameter {list.add(p);}
        (COMMA p=asmRuleTypeRefNamedParameter {list.add(p);})?
        {
            l = (AstParameter[]) list.toArray(new AstParameter[list.size()]);
        }
    ;

protected
predicateNamedParameters returns [AstParameter[] args = null]
{
    AstParameter[] rules=null;
}
    :
        (
            LPAREN (COLON rules=asmRuleTypeRefNamedParameterList SEMI)?
            (
                args = formulaOrTypeRefNamedParameterList RPAREN
                {
                    if (rules != null) {
                        AstParameter[] olds=args;
                        args=new AstParameter[olds.length + rules.length];
                        for(int i=0;i<rules.length;i++) { args[i] = rules[i]; }
                        for(int i=rules.length; i<args.length; i++)
                        {args[i] = olds[i-rules.length];}
                    }
                }
            |
                RPAREN
            )
        )?
        {
            if (args == null) { 
                args = rules==null?EMPTY_PARAMETERS:rules;
            }
        }
    ;



 
/** Now we can turn to the definitions themselves */   

protected 
unitDeclaration returns [Identifier u]
    :
        unit_:UNIT u=bigident (SEMI)?
    ;

protected
exportDeclaration returns [AstExport e=null]
{
    AstRestrictedSymbol[] symbs;
}
    :
        (
            export:EXPORT 
            (
                ASTERIX { e = af.createAllSymbolsAstExport(createLocation(export));}
            |
                LPAREN symbs=importedSymbolList RPAREN
                {
                    e = af.createSomeSymbolsAstExport(createLocation(export), symbs);
                }
            )
            (SEMI)?
        )?
        {
            if(e==null) { e = af.createNoSymbolsAstExport(); }
        }
    ;

protected
useImportDeclaration returns [AstImport i]
{
    Identifier unit;
    AstRestrictedSymbol[] symbs;
}
    :
        (
            use:USE unit=bigident {i = af.createNoSymbolsAstImport(createLocation(use), unit);}
        |
            import_:IMPORT
            (
                ASTERIX {symbs = null;}
            |
                LPAREN symbs=importedSymbolList RPAREN
            )
            FROM unit=bigident
            {
                if (symbs == null) {
                    i = af.createAllSymbolsAstImport(createLocation(import_), unit);
                } else {
                    i = af.createSomeSymbolsAstImport(createLocation(import_), unit, symbs);
                }
            }
        )
        (SEMI)?
    ;

protected
useImportDeclarationList returns [AstImport[] is]
{
    AstImport i;
    List list = createList();
}
    :
        (
            i=useImportDeclaration
            {
                list.add(i);
            }
        )*
        {
            is = ((AstImport[]) list.toArray(new AstImport[list.size()]));
        }
    ;

protected
importedSymbols returns [AstRestrictedSymbol[] symbs]
{
    List list = createList();
    int type;
    Identifier[] ids;
}
    :
        (
            SORT {type = AstRestrictedSymbol.SORT;}
        |
            SCHEMA VARIABLE {type = AstRestrictedSymbol.SCHEMA_VARIABLE;}
        |
            FUNCTION {type = AstRestrictedSymbol.FUNCTION;}
        |
            PREDICATE {type = AstRestrictedSymbol.FUNCTION;}
        |
            ASM { type = AstRestrictedSymbol.ASMRULE; }
        |
            TACLET { type = AstRestrictedSymbol.TACLET; }
        |
            PROPOSITION { type = AstRestrictedSymbol.PROPOSITION; }
        )
        ids = identList
        {
            symbs = createAstRestrictedSymbols(type, ids);
        }
    ; 

protected
importedSymbolList returns [AstRestrictedSymbol[] symbs]
{
    List list = createList();
    AstRestrictedSymbol[] tmp_symbs;
}
    :
        tmp_symbs=importedSymbols
        {
            list.addAll(Arrays.asList(tmp_symbs));
        }
        (
            SEMI tmp_symbs=importedSymbols
            {
                list.addAll(Arrays.asList(tmp_symbs));
            }

        )*
        {
            symbs = (AstRestrictedSymbol[]) list.toArray(new AstRestrictedSymbol[list.size()]);
        }
    ;
            

protected
sortDecl returns [AstSinglePassDeclaration decl]
{
    Identifier id;
    Identifier[] ids=null;
    boolean isGenericSort=false;
    AstType type = null;
}
    :
        (GENERIC {isGenericSort=true;})? SORT id=singleident 
        (EQUALS {!isGenericSort}? ids=identBarList)?
        (SEMI)?
        {
            if (ids == null) {
                decl = af.createPrimitiveSortDeclaration(id.getLocation(), id, isGenericSort);
            } else {
                decl = af.createEnumeratedSortDeclaration(id.getLocation(), id, ids);
            }
        }
    ;



protected
schemaVarDecl returns [AstSinglePassDeclaration[] decls]
{
	AstSchemaType r;
    Identifier[] l;
}
    :
        SCHEMA r=schemaTypeRef l=identList (SEMI)?
        {
            decls = new AstSinglePassDeclaration[l.length];
            for (int i = 0; i < l.length; ++i) {
                decls[i] = af.createSchemaVariableDeclaration(r.getLocation(), l[i], r);
            }
        }
    ;

protected
predicateDecl returns [AstDeclaration decl]
{   
    Identifier id;
    AstType[] args;
    AstParameter[] params;
    boolean dynamic = false;
    AstTerm t = null;
}
    :
        (
            der:DERIVED PREDICATE
            id=ident params=predicateNamedParameters EQUALS t=formula
            {
                decl = af.createDerivedPredicateDeclaration(createLocation(der), id, params, t);
            }
        |
            PREDICATE id=ident args=predicateParameters
            {
                decl = af.createPredicateDeclaration(id.getLocation(), id, args);
            }
        )
        (SEMI)?
    ;



protected
functionDecl returns [AstDeclaration decl]
{
    AstType ret;
    Identifier id;
	AstType[] args=null;
    AstParameter[] params;
    boolean dynamic;
    Location location;
    AstTerm t = null;
}
	:
        (
            der:DERIVED FUNCTION
            ret=typeRef id=ident params=typeRefNamedParameters EQUALS t=term
            {
                decl = af.createDerivedFunctionDeclaration(createLocation(der), id, params, ret, t);
            }
        |
            (
                d:DYNAMIC 
                { 
                    dynamic = true;
                    location = createLocation(d);
                }
            |
                s:STATIC
                {
                    dynamic = false;
                    location = createLocation(s);
                }
            )
            FUNCTION
            ret=typeRef id=ident args=typeRefParameters
            {
                decl = af.createFunctionDeclaration(location,
                    id, args, ret, dynamic);
            }
        )
        (SEMI)?
	;


protected
tacletDecl returns [AstTacletDeclaration decl]
{
    Identifier id;
    AstTaclet t;
}
    :
		TACLET id=ident LBRACE
        t=taclet
        RBRACE (SEMI)?
        {
            decl = new AstTacletDeclaration(id.getLocation(), id, t);
        }
    ;

protected
namedRuleDecl returns [AstDeclaration d]
{
    Identifier id;
    AstParameter[] params;
    AstAsmRule r;
}
    :
        (
            ABSTRACT ASM
            id = bigident
            {
                d = af.createAbstractAsmRuleDeclaration(id.getLocation(), id);
            }
        |
            ASM id=bigident 
            params=typeRefNamedParameters 
            EQUALS r=asmRule (SEMI)?
            {
                d = af.createNamedRuleDeclaration(id.getLocation(), id, params, r);
            }
        )
    ;

protected
lemmaDecl returns [AstSinglePassDeclaration d]
{
    Identifier id;
    AstTerm phi;
    AstParameter[] params;
}
    :
        LEMMA id=ident params=predicateNamedParameters EQUALS 
        phi=formula (SEMI)?
        {
            d = af.createLemmaDeclaration(id.getLocation(), id, params, phi);
        }
    ;

protected
ruleSetDecl returns [AstSinglePassDeclaration d]
{
    Identifier id;
}
    :
        RULE SET id=ident (SEMI)?
        {
            d = af.createRuleSetDeclaration(id.getLocation(), id);
        }
    ;

protected
metaDecl returns [AstSinglePassDeclaration d]
{
    Identifier id;
}
    :
        META (id = ident | id = bigident) (SEMI)? 
        {
            d = af.createMetaOperatorDeclaration(id.getLocation(), id);
        }
    ;

protected
earlySinglePassDeclaration returns [AstSinglePassDeclaration d]
    :
        (
            d=sortDecl
        |
            d=ruleSetDecl
        |
            d=metaDecl
        )
    ;

protected
earlySinglePassDeclarations returns [AstSinglePassDeclaration[] decls]
    :
        decls=schemaVarDecl
    ;

protected
multiplePassDeclaration returns [AstDeclaration d]
    :
        d=predicateDecl
    |
        d=functionDecl
    |
        d=namedRuleDecl
    ;

protected
lateSinglePassDeclaration returns [AstSinglePassDeclaration d]
    :
        d=tacletDecl
    |
        d=lemmaDecl
    ;

protected 
declarationList returns [AstUnitDeclarations decls]
{
    AstSinglePassDeclaration d;
    AstSinglePassDeclaration[] ds;
    AstDeclaration m;
    List early = createList();
    List multi = createList();
    List late = createList();
}
    :
        (
            d=earlySinglePassDeclaration
            {
                early.add(d);
            }
        |
            ds=earlySinglePassDeclarations
            {
                early.addAll(Arrays.asList(ds));
            }
        |
            m=multiplePassDeclaration
            {
                if (m instanceof AstMultiPassDeclaration) {
                    multi.add(m);
                } else {
                    early.add(m);
                }
            }
        |
            d=lateSinglePassDeclaration
            {
                late.add(d);
            }
        )*
        {
            decls = new AstUnitDeclarations(
                (AstSinglePassDeclaration[]) early.toArray(
                    new AstSinglePassDeclaration[early.size()]),
                (AstMultiPassDeclaration[]) multi.toArray(
                    new AstMultiPassDeclaration[multi.size()]),
                (AstSinglePassDeclaration[]) late.toArray(
                    new AstSinglePassDeclaration[late.size()]));
        }
    ;

/* unit file */

unit returns [AstUnit u]
{
    Identifier unit;
    AstExport export;
    AstImport[] imports;
    AstUnitDeclarations decls;
}
    :
        unit=unitDeclaration
        export=exportDeclaration
        imports=useImportDeclarationList
        decls=declarationList
        {
            u = af.createAstUnit(unit.getLocation(), unit, export, imports, decls);
        }
    ;


/* proof */


proof returns [AstProof p]
{
    AstProofExpression pe;
    AstProofExpression[] pl;
    AstProofMeta m;
    AstTerm t;
}
    :
        m=proofMeta
        problem:PROBLEM LBRACE
        t =formula
        RBRACE
        (
            PROOF LBRACE pl=proof_logs pe=proof_expr RBRACE
            {
                p = af.createPropAstProof(createLocation(problem), m, t, pl, pe);
            }
        |
            AXIOM
            {
                p = af.createAxiomAstProof(createLocation(problem), m, t);
            }
        |   
            TRUTH
            {
                p = af.createTruthAstProof(createLocation(problem), m, t);
            }
        )
    ;

protected
proofMeta returns [AstProofMeta m]
{
    Identifier id;
    String header;
    boolean closed;
}
    :
        META LBRACE
        HEADER EQUALS header_str:STRING_LITERAL { header = header_str.getText(); }
        NAME EQUALS id=ident
        CLOSED EQUALS
        ( TRUE {closed = true;} | FALSE {closed = false;} )
        RBRACE
        {
            m = new AstProofMeta(id, header, closed);
        }
    ;

protected
proof_logs returns [AstProofExpression[] pl = null]
{
    List list = createList();
    AstProofExpression pe;
}
    :
        (
            pe = log_entry
            {
                list.add(pe);
            }
        )*
        {
            pl = (AstProofExpression[]) list.toArray(new AstProofExpression[list.size()]);
        }
    ;

protected
log_entry returns [AstProofExpression pe]
{
    String num;
    String user;
    String version;
}
    :
        paren:LPAREN
        LOG num_str:STRING_LITERAL { num = num_str.getText(); }
        user_loc:LPAREN USER user_str:STRING_LITERAL { user = user_str.getText(); } RPAREN
        version_loc:LPAREN VERSION version_str:STRING_LITERAL
          { version = version_str.getText(); } RPAREN
        RPAREN
        {
            pe =  new AstProofExpression
             (createLocation(paren),
              AstProofExpressionType.LOG,
              num,
              new AstProofExpression[]
                {
                    new AstProofExpression(createLocation(user_loc),
                                           AstProofExpressionType.USER,
                                           user,
                                           new AstProofExpression[0]),
                    new AstProofExpression(createLocation(version_loc),
                                           AstProofExpressionType.VERSION,
                                           version,
                                           new AstProofExpression[0])
                }
             );
        }
    ;

protected
proof_expr returns [AstProofExpression pe = null]
{
    AstProofExpression child;
    AstProofExpressionType type;
    List list = createList();
    String id = null;
}
    :
        paren:LPAREN
        (
            type=proof_expr_type
            (
                str:STRING_LITERAL
                {
                    id = str.getText();
                }
            )?
            (
                child=proof_expr
                {
                    list.add(child);
                }
            )*
            {
                AstProofExpression[] children = (AstProofExpression[]) list.toArray(new AstProofExpression[list.size()]);
                pe = new AstProofExpression(createLocation(paren), type, id, children);
            }
        )?
        RPAREN
    ;


/* Das ist aus der Parser-Spezifikation des Java-KeY-Systems. Ich
verstehe allerdings nicht, was der allgemeine (und ungenutzte) IDENT
hier soll. Er wird beispielsweise bei "opengoal" verwendet. */
protected
proof_expr_type returns [AstProofExpressionType type]
    :
        (
            FORMULA
            {
                type = AstProofExpressionType.FORMULA;
            }
        |
            TERM
            {
                type = AstProofExpressionType.TERM;
            }
        |
            BUILTIN
            {
                type = AstProofExpressionType.BUILTIN;
            }
        |
            RULE
            {
                type = AstProofExpressionType.RULE;
            }
        | 
            BRANCH
            {
                type = AstProofExpressionType.BRANCH;
            }
        |   
            INST
            {
                type = AstProofExpressionType.INST;
            }
        |
            IFSEQFORMULA
            { 
                type = AstProofExpressionType.IFSEQFORMULA;
            }
        |
            INTERACTIVE
            { 
                type = AstProofExpressionType.INTERACTIVE;
            }
        |
            HEUR
            {
                type = AstProofExpressionType.HEURISTICS;
            }
        |
            IDENT
            {
                type = AstProofExpressionType.IDENT;
            }
        )
    ;

/* proof file */
