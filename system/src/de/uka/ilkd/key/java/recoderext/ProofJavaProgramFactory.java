// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
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
import recoder.ServiceConfiguration;
import recoder.convenience.TreeWalker;
import recoder.io.ProjectSettings;
import recoder.io.PropertyNames;
import recoder.java.*;
import recoder.java.SourceElement.Position;
import recoder.java.declaration.*;
import recoder.java.reference.MethodReference;
import recoder.java.reference.TypeReference;
import recoder.java.reference.VariableReference;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.util.StringUtils;
import de.uka.ilkd.key.java.recoderext.adt.MethodSignature;
import de.uka.ilkd.key.parser.proofjava.ParseException;
import de.uka.ilkd.key.parser.proofjava.ProofJavaParser;

public class ProofJavaProgramFactory extends JavaProgramFactory {
    
    /**
     Protected constructor - use {@link #getInstance} instead.
     */
    protected ProofJavaProgramFactory() {}

    /** 
     The singleton instance of the program factory.
     */
    private static ProofJavaProgramFactory theFactory 
	= new ProofJavaProgramFactory();

    /** 
     Returns the single instance of this class.
     */
    public static JavaProgramFactory getInstance() {
        return theFactory;
    }
    
    public void initialize(ServiceConfiguration cfg) {

      super.initialize(cfg);
      ProjectSettings settings = cfg.getProjectSettings();
      /*// that is the original recoder code:
      ProofJavaParser.setAwareOfAssert(StringUtils.parseBooleanProperty(settings.getProperties().getProperty(
              PropertyNames.JDK1_4)));
      ProofJavaParser.setJava5(ALLOW_JAVA5); 
      */
      ProofJavaParser.setJava5(StringUtils.parseBooleanProperty(settings.getProperties().getProperty(
              PropertyNames.JAVA_5)));
      ProofJavaParser.setAwareOfAssert(true);
      
  }


    /** 
     For internal reuse and synchronization.
     */
    private static final ProofJavaParser parser = new ProofJavaParser(System.in);

    private static final Position ZERO_POSITION = new Position(0, 0);

    private static void attachComment(Comment c, ProgramElement pe) {
        ProgramElement dest = pe;
        if (!c.isPrefixed()) {
            NonTerminalProgramElement ppe = dest.getASTParent();
            int i = 0;
            if (ppe != null) {
                for (; ppe.getChildAt(i) != dest; i++) {}
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
        List<Comment> comments = ProofJavaParser.getComments();
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
		    current.setPrefixed(true);
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
		ProofJavaParser.initialize(in);
		CompilationUnit res = ProofJavaParser.CompilationUnit();
		postWork(res);
		return res;
	    } catch (ParseException e) {
		throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
	    }
        }
    }

    /**
     Parse a {@link TypeDeclaration} from the given reader.
     */
    public TypeDeclaration parseTypeDeclaration(Reader in) throws IOException, ParserException {
        synchronized(parser) {
	    try{
		ProofJavaParser.initialize(in);
		TypeDeclaration res = ProofJavaParser.TypeDeclaration();
		postWork(res);
		return res;
	    } catch (ParseException e) {
		throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
	    }

        }
    }

    /**
     Parse a {@link FieldDeclaration} from the given reader.
     */
    public FieldDeclaration parseFieldDeclaration(Reader in) throws IOException, ParserException {
        synchronized(parser) {
	    try{
		ProofJavaParser.initialize(in);
		FieldDeclaration res = ProofJavaParser.FieldDeclaration();
		postWork(res);
		return res;
	    } catch (ParseException e) {
		throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
	    }

        }
    }

    /**
     Parse a {@link MethodDeclaration} from the given reader.
     */
    public MethodDeclaration parseMethodDeclaration(Reader in) throws IOException, ParserException {
        synchronized(parser) {
	    try{
		ProofJavaParser.initialize(in);
		MethodDeclaration res = ProofJavaParser.MethodDeclaration();
		postWork(res);
		return res;
	    } catch (ParseException e) {
		throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
	    }

        }
    }

    /**
     Parse a {@link MemberDeclaration} from the given reader.
     */
    public MemberDeclaration parseMemberDeclaration(Reader in) throws IOException, ParserException {
        synchronized(parser) {
	    try{
		ProofJavaParser.initialize(in);
		MemberDeclaration res = ProofJavaParser.ClassBodyDeclaration();
		postWork(res);
		return res;
	    } catch (ParseException e) {
		throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
	    }

        }
    }

    /**
     Parse a {@link ParameterDeclaration} from the given reader.
     */
    public ParameterDeclaration parseParameterDeclaration(Reader in) throws IOException, ParserException {
        synchronized(parser) {
	    try{
		ProofJavaParser.initialize(in);
		ParameterDeclaration res = ProofJavaParser.FormalParameter();
		postWork(res);
		return res;
	    } catch (ParseException e) {
		throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
	    }

        }
    }

    /**
     Parse a {@link ConstructorDeclaration} from the given reader.
     */
    public ConstructorDeclaration parseConstructorDeclaration(Reader in) throws IOException, ParserException {
        synchronized(parser) {
	    try{
		ProofJavaParser.initialize(in);
		ConstructorDeclaration res = ProofJavaParser.ConstructorDeclaration();
		postWork(res);
		return res;
	    } catch (ParseException e) {
		throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
	    }

        }
    }

    /**
     Parse a {@link TypeReference} from the given reader.
     */
    public TypeReference parseTypeReference(Reader in) throws IOException, ParserException {
        synchronized(parser) {
	    try{
		ProofJavaParser.initialize(in);
		TypeReference res = ProofJavaParser.ResultType();
		postWork(res);
		return res;
	    } catch (ParseException e) {
		throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
	    }

        }
    }

    /**
     Parse an {@link Expression} from the given reader.
     */
    public Expression parseExpression(Reader in) throws IOException, ParserException {
        synchronized(parser) {
	    try{
		ProofJavaParser.initialize(in);
		Expression res = ProofJavaParser.Expression();
		postWork(res);
		return res;
	    } catch (ParseException e) {
		throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
	    }

        }
    }

    /**
     Parse some {@link Statement}s from the given reader.
     */
    public ASTList<Statement> parseStatements(Reader in) throws IOException, ParserException {
        synchronized(parser) {
	    try{
		ProofJavaParser.initialize(in);
		ASTList<Statement> res = ProofJavaParser.GeneralizedStatements();
		for (int i = 0; i < res.size(); i += 1) {
		    postWork(res.get(i));
		}
		return res;
	    } catch (ParseException e) {
		throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
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
		ProofJavaParser.initialize(in);
		StatementBlock res = ProofJavaParser.StartBlock();
		postWork(res);
		return res;
	    } catch (ParseException e) {
		throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
	    }

        }
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

    /**
     * Create a {@link MethodSignature}.
     */
    public MethodSignature createMethodSignature(Identifier methodName,
        ASTList<TypeReference> paramTypes) {
       return new MethodSignature(methodName, paramTypes);
    }

    /**
     * Create a {@link MethodCallStatement}.
     */
    public MethodCallStatement createMethodCallStatement(Expression resVar,
							 ExecutionContext ec,
							 StatementBlock block) {
	return new MethodCallStatement(resVar, ec, block);
    }

    /**
     * Create a {@link MethodBodyStatement}.
     */
    public MethodBodyStatement createMethodBodyStatement(TypeReference bodySource,
							 Expression resVar,
							 MethodReference methRef) {
	return new MethodBodyStatement(bodySource, resVar, methRef);
    }

    /**
     * Create a {@link CatchAllStatement}.
     */
    public Statement createCatchAllStatement(VariableReference param,
					     StatementBlock body) {
	return new CatchAllStatement(param, body);
    }
    
    /**
     * Create a comment.
     * @param text comment text
     */
    public Comment createComment(String text) {
        return new Comment(text);
    }
    
    /**
     * Create a comment.
     * @param text comment text
     */
    public Comment createComment(String text, boolean prefixed) {
        return new Comment(text, prefixed);
    }
    
    /**
     * Create an {@link ImplicitIdentifier}.
     */
    public ImplicitIdentifier createImplicitIdentifier(String text) {
        return new ImplicitIdentifier(text);
    }


    public Identifier createIdentifier(String text) {
        return new ExtendedIdentifier(text);
    }
    
    public ObjectTypeIdentifier createObjectTypeIdentifier(String text) {
        return new ObjectTypeIdentifier(text);
    }
    
}