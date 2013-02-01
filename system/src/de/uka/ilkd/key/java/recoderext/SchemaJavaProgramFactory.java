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


// This file is partially taken from the RECODER library, which is protected by 
// the LGPL, and modified.


package de.uka.ilkd.key.java.recoderext;

import java.io.IOException;
import java.io.Reader;
import java.util.List;

import recoder.ParserException;
import recoder.convenience.TreeWalker;
import recoder.java.*;
import recoder.java.SourceElement.Position;
import recoder.java.declaration.*;
import recoder.java.reference.MethodReference;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.TypeReference;
import recoder.list.generic.*;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.parser.schemajava.ParseException;
import de.uka.ilkd.key.parser.schemajava.SchemaJavaParser;

public class SchemaJavaProgramFactory extends JavaProgramFactory {

    protected Namespace svns;

    /**
     Protected constructor - use {@link #getInstance} instead.
     */
    protected SchemaJavaProgramFactory() {}

    /** 
     The singleton instance of the program factory.
     */
    private static SchemaJavaProgramFactory theFactory 
	= new SchemaJavaProgramFactory();

    /** 
     Returns the single instance of this class.
     */
    public static JavaProgramFactory getInstance() {
        return theFactory;
    }

    /**
     * Create an {@link ImplicitIdentifier}.
     */
    public ImplicitIdentifier createImplicitIdentifier(String text) {
        return new ImplicitIdentifier(text);
    }
    
    public Identifier createIdentifier (String text){
        return new ExtendedIdentifier(text);
    }

    public SpecialReferenceWrapper createThisReference(TypeReference typeRef,
						       Expression var) {
	return new SpecialReferenceWrapper
	    (typeRef, (ReferencePrefix) var);
    }

    public RMethodCallStatement createRMethodCallStatement(ProgramVariableSVWrapper resVar,
							   ExecutionContext esvw,
							   Statement st) {
	return new RMethodCallStatement(resVar, esvw, st);
    }
    
    public RMethodBodyStatement createRMethodBodyStatement
            (TypeReference typeRef,
             ProgramVariableSVWrapper resVar,
             MethodReference mr) {
        return new RMethodBodyStatement(typeRef, resVar, mr);
    }

    public RKeYMetaConstruct createRKeYMetaConstruct() {
	return new RKeYMetaConstruct();
    }

    public RKeYMetaConstructExpression createRKeYMetaConstructExpression() {
	return new RKeYMetaConstructExpression();
    }


    public RKeYMetaConstructType createRKeYMetaConstructType() {
	return new RKeYMetaConstructType();
    }

    public ContextStatementBlock createContextStatementBlock(TypeSVWrapper typeRef,
                          MethodSignatureSVWrapper pm,
							     ExpressionSVWrapper var) {
	return new ContextStatementBlock(typeRef, pm, var);
    }

    public ContextStatementBlock createContextStatementBlock(ExecCtxtSVWrapper ec) {
	return new ContextStatementBlock(ec);
    }

    /**
     * Create a {@link PassiveExpression}.
     */
    public PassiveExpression createPassiveExpression(Expression e) {
	return new PassiveExpression(e);
    }

    /**
     * Create a {@link PassiveExpression}.
     */
    public PassiveExpression createPassiveExpression() {
	return new PassiveExpression();
    }

    public static void throwSortInvalid(SchemaVariable sv, String s) 
	throws ParseException {
	throw new ParseException("Sort of declared schema variable "
				  +sv.name().toString()+" "
				  +sv.sort().name().toString()
				  +" does not comply with expected type "+s
				  +" in Java program.");
    }


    public boolean lookupSchemaVariableType(String s, ProgramSVSort sort) {
	if (svns==null) return false;
	Named n=svns.lookup(new Name(s));
	if (n!=null && n instanceof SchemaVariable) {
	    return ((SchemaVariable) n).sort()==sort;
	} 
	return false;
    }


    public SchemaVariable lookupSchemaVariable(String s) throws ParseException {
	SchemaVariable sv=null;
	Named n=svns.lookup(new Name(s));
	if (n!=null && n instanceof SchemaVariable) {
	    sv=(SchemaVariable) n;
	} else {
	    throw new ParseException("Schema variable not declared: "+s);
	}
	return sv;
    }

    public StatementSVWrapper getStatementSV(String s) throws ParseException {
	SchemaVariable sv=lookupSchemaVariable(s);
	if (!(sv instanceof ProgramSV)) {   
	    throwSortInvalid(sv, "Statement");
	}

	return new StatementSVWrapper(sv);
    }

    public ExpressionSVWrapper getExpressionSV(String s) throws ParseException {
	SchemaVariable sv=lookupSchemaVariable(s);
	if (!(sv instanceof ProgramSV)) {   
	    throwSortInvalid(sv, "Expression");
	}
	return new ExpressionSVWrapper(sv);
    }


    public LabelSVWrapper getLabelSV(String s) throws ParseException{
	SchemaVariable sv=lookupSchemaVariable(s);
	if (!(sv instanceof ProgramSV)) {   
	    throwSortInvalid(sv, "Label");
	}
	return new LabelSVWrapper(sv);
    }
    
    public MethodSignatureSVWrapper getMethodSignatureSVWrapper(String s) throws ParseException{
       SchemaVariable sv=lookupSchemaVariable(s);
       if (!(sv instanceof ProgramSV)) {   
           throwSortInvalid(sv, "MethodSignature");
       }
       return new MethodSignatureSVWrapper(sv);
        }
    
    public JumpLabelSVWrapper getJumpLabelSV(String s) throws ParseException {
        SchemaVariable sv=lookupSchemaVariable(s);
        if (!(sv instanceof ProgramSV) ||
                sv.sort()!=ProgramSVSort.LABEL) {   
            throwSortInvalid(sv, "Label");
        }
        return new JumpLabelSVWrapper(sv);
    }

    public TypeSVWrapper getTypeSV(String s) throws ParseException{
	SchemaVariable sv=lookupSchemaVariable(s);
	if (!(sv instanceof ProgramSV)) {   
	    throwSortInvalid(sv, "Type");
	}
	return new TypeSVWrapper(sv);
    }

    public ExecCtxtSVWrapper getExecutionContextSV(String s) throws ParseException {
	SchemaVariable sv=lookupSchemaVariable(s);
	if (!(sv instanceof ProgramSV)) {   
	    throwSortInvalid(sv, "Type");
	}
	return new ExecCtxtSVWrapper(sv);
    }

    public ProgramVariableSVWrapper getProgramVariableSV(String s) 
	throws ParseException{
	SchemaVariable sv=lookupSchemaVariable(s);
	if (!(sv instanceof ProgramSV)) {   
	    throwSortInvalid(sv, "Program Variable");
	}
	return new ProgramVariableSVWrapper(sv);
    }

    public CatchSVWrapper getCatchSV(String s) 
	throws ParseException {
	SchemaVariable sv=lookupSchemaVariable(s);
	if (!(sv instanceof ProgramSV)) {   
	    throwSortInvalid(sv, "Catch");
	}
	return new CatchSVWrapper(sv);
    }




    /** 
     For internal reuse and synchronization.
     */
    private static SchemaJavaParser parser = new SchemaJavaParser(System.in);

    private static final Position ZERO_POSITION = new Position(0, 0);

    private static void attachComment(Comment c, ProgramElement pe) {
        ProgramElement dest = pe;
        if (!c.isPrefixed()) {
            NonTerminalProgramElement ppe = dest.getASTParent();
            int i = 0;
            if (ppe != null) {
                for (; ppe.getChildAt(i) != dest; i++){}
            }
            if (i == 0) { // before syntactical parent
		c.setPrefixed(true);
            } else {
                dest = ppe.getChildAt(i - 1);
                while (dest instanceof NonTerminalProgramElement) {
                    ppe = (NonTerminalProgramElement)dest;
                    i = ppe.getChildCount();
                    if (i == 0) {
                        break;
                    }
                    dest = ppe.getChildAt(i - 1);
                }
            }
        }
        if (c instanceof SingleLineComment && c.isPrefixed()) {
            Position p = dest.getFirstElement().getRelativePosition();
            if (p.getLine() < 1) {
                p.setLine(1);
                dest.getFirstElement().setRelativePosition(p);
            }
        }
        ASTList<Comment> cml = dest.getComments();
        if (cml == null) {
            dest.setComments(cml = new ASTArrayList<Comment>());
        }
        cml.add(c);
    }

    /**
       Perform post work on the created element. Creates parent links
       and assigns comments.
     */
    private static void postWork(ProgramElement pe) {     
        List<Comment> comments = SchemaJavaParser.getComments();
        int commentIndex = 0;
        int commentCount = comments.size();
        Position cpos = ZERO_POSITION;
        Comment current = null;
        if (commentIndex < commentCount) {
            current = comments.get(commentIndex);
            cpos = current.getFirstElement().getStartPosition();
        }
        TreeWalker tw = new TreeWalker(pe);
        while (tw.next()) {
            pe = tw.getProgramElement();
            if (pe instanceof NonTerminalProgramElement) {
                ((NonTerminalProgramElement)pe).makeParentRoleValid();
            }
	    if (pe.getFirstElement()!=null) {
		Position pos = pe.getFirstElement().getStartPosition();
		while ((commentIndex < commentCount) 
		       && pos.compareTo(cpos) > 0) {
		    attachComment(current, pe);
		    commentIndex += 1;
		    if (commentIndex < commentCount) {
			current = comments.get(commentIndex);
			cpos = current.getFirstElement().getStartPosition();
		    }
		}
            }
        }
        if (commentIndex < commentCount) {
            while (pe.getASTParent() != null) {
                pe = pe.getASTParent();
            }
            ASTList<Comment> cml = pe.getComments();
            if (cml == null) {
                pe.setComments(cml = new ASTArrayList<Comment>());
            }
            do {
                current = comments.get(commentIndex);
                current.setPrefixed(false);
                cml.add(current);
                commentIndex += 1;
            } while (commentIndex < commentCount);
        }
    }

    /**
     Parse a {@link CompilationUnit} from the given reader.
     */
    public CompilationUnit parseCompilationUnit(Reader in) throws IOException, ParserException {
        synchronized(parser) {
	    try {
		SchemaJavaParser.initialize(in);
		CompilationUnit res = SchemaJavaParser.CompilationUnit();
		postWork(res);
		return res;
	    } catch (ParseException e) {
	        ParserException pe = new ParserException();
	        pe.initCause(e);
		throw pe;
	    }
        }
    }

    /**
     Parse a {@link TypeDeclaration} from the given reader.
     */
    public TypeDeclaration parseTypeDeclaration(Reader in) throws IOException, ParserException {
        synchronized(parser) {
	    try{
		SchemaJavaParser.initialize(in);
		TypeDeclaration res = SchemaJavaParser.TypeDeclaration();
		postWork(res);
		return res;
	    } catch (ParseException e) {
	        ParserException pe = new ParserException();
                pe.initCause(e);
                throw pe;
	    }

        }
    }

    /**
     Parse a {@link FieldDeclaration} from the given reader.
     */
    public FieldDeclaration parseFieldDeclaration(Reader in) throws IOException, ParserException {
        synchronized(parser) {
	    try{
		SchemaJavaParser.initialize(in);
		FieldDeclaration res = SchemaJavaParser.FieldDeclaration();
		postWork(res);
		return res;
	    } catch (ParseException e) {
	        ParserException pe = new ParserException();
                pe.initCause(e);
                throw pe;
	    }

        }
    }

    /**
     Parse a {@link MethodDeclaration} from the given reader.
     */
    public MethodDeclaration parseMethodDeclaration(Reader in) throws IOException, ParserException {
        synchronized(parser) {
	    try{
		SchemaJavaParser.initialize(in);
		MethodDeclaration res = SchemaJavaParser.MethodDeclaration();
		postWork(res);
		return res;
	    } catch (ParseException e) {
	        ParserException pe = new ParserException();
                pe.initCause(e);
                throw pe;
	    }

        }
    }

    /**
     Parse a {@link MemberDeclaration} from the given reader.
     */
    public MemberDeclaration parseMemberDeclaration(Reader in) throws IOException, ParserException {
        synchronized(parser) {
	    try{
		SchemaJavaParser.initialize(in);
		MemberDeclaration res = SchemaJavaParser.ClassBodyDeclaration();
		postWork(res);
		return res;
	    } catch (ParseException e) {
	        ParserException pe = new ParserException();
                pe.initCause(e);
                throw pe;
	    }

        }
    }

    /**
     Parse a {@link ParameterDeclaration} from the given reader.
     */
    public ParameterDeclaration parseParameterDeclaration(Reader in) throws IOException, ParserException {
        synchronized(parser) {
	    try{
		SchemaJavaParser.initialize(in);
		ParameterDeclaration res = SchemaJavaParser.FormalParameter();
		postWork(res);
		return res;
	    } catch (ParseException e) {
	        ParserException pe = new ParserException();
                pe.initCause(e);
                throw pe;
	    }

        }
    }

    /**
     Parse a {@link ConstructorDeclaration} from the given reader.
     */
    public ConstructorDeclaration parseConstructorDeclaration(Reader in) throws IOException, ParserException {
        synchronized(parser) {
	    try{
		SchemaJavaParser.initialize(in);
		ConstructorDeclaration res = SchemaJavaParser.ConstructorDeclaration();
		postWork(res);
		return res;
	    } catch (ParseException e) {
	        ParserException pe = new ParserException();
                pe.initCause(e);
                throw pe;
	    }

        }
    }

    /**
     Parse a {@link TypeReference} from the given reader.
     */
    public TypeReference parseTypeReference(Reader in) throws IOException, ParserException {
        synchronized(parser) {
	    try{
		SchemaJavaParser.initialize(in);
		TypeReference res = SchemaJavaParser.ResultType();
		postWork(res);
		return res;
	    } catch (ParseException e) {
	        ParserException pe = new ParserException();
                pe.initCause(e);
                throw pe;
	    }

        }
    }

    /**
     Parse an {@link Expression} from the given reader.
     */
    public Expression parseExpression(Reader in) throws IOException, ParserException {
        synchronized(parser) {
	    try{
		SchemaJavaParser.initialize(in);
		Expression res = SchemaJavaParser.Expression();
		postWork(res);
		return res;
	    } catch (ParseException e) {
	        ParserException pe = new ParserException();
                pe.initCause(e);
                throw pe;
	    }

        }
    }

    /**
     Parse some {@link Statement}s from the given reader.
     */
    public ASTList<Statement> parseStatements(Reader in) throws IOException, ParserException {
        synchronized(parser) {
	    try{
		SchemaJavaParser.initialize(in);
		ASTList<Statement> res = SchemaJavaParser.GeneralizedStatements();
		for (int i = 0; i < res.size(); i += 1) {
		    postWork(res.get(i));
		}
		return res;
	    } catch (ParseException e) {
	        ParserException pe = new ParserException();
                pe.initCause(e);
                throw pe;
	    }

        }
    }

    /**
     * Parse a {@link StatementBlock} from the given string.
     */
    public StatementBlock parseStatementBlock(Reader in) 
	throws IOException, ParserException {
	synchronized(parser) {
	    try{
		SchemaJavaParser.initialize(in);
		StatementBlock res = SchemaJavaParser.StartBlock();
		postWork(res);
		return res;
	    } catch (ParseException e) {
	        ParserException pe = new ParserException(e.getMessage());
                pe.initCause(e);
                throw pe;
	    }

        }
    }



    public void setSVNamespace(Namespace ns) {
	svns=ns;
    }
}
