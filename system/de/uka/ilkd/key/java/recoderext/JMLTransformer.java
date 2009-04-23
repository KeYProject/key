// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.recoderext;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;

import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.collection.SLListOfString;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.SetAsListOfPositionedString;
import de.uka.ilkd.key.speclang.SetOfPositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.Constructor;
import recoder.abstraction.Method;
import recoder.io.DataLocation;
import recoder.java.*;
import recoder.java.SourceElement.Position;
import recoder.java.declaration.*;
import recoder.java.expression.operator.CopyAssignment;
import recoder.java.statement.EmptyStatement;
import recoder.list.generic.*;


public class JMLTransformer extends RecoderModelTransformer {
    
    private static final ListOfString javaMods
        = SLListOfString.EMPTY_LIST.prepend(new String[]{"abstract",
                                                         "final", 
                                                         "private", 
                                                         "protected", 
                                                         "public", 
                                                         "static"});    
    
    private static SetOfPositionedString warnings;
    

    /**
     * Creates a transformation that adds JML specific elements, for example
     * ghost fields and model method declarations.
     * 
     * @param services
     *                the CrossReferenceServiceConfiguration to access model
     *                information
     * @param cache
     *                a cache object that stores information which is needed by
     *                and common to many transformations. it includes the
     *                compilation units, the declared classes, and information
     *                for local classes.
     */
    public JMLTransformer(CrossReferenceServiceConfiguration services,
                          TransformerCache cache) {
        super(services, cache);
        warnings = SetAsListOfPositionedString.EMPTY_SET;
    }

   
    
    //-------------------------------------------------------------------------
    //private helper methods
    //-------------------------------------------------------------------------
    
    /**
     * Concatenates the passed comments in a position-preserving way.
     * (see also JMLSpecExtractor::concatenate(), which does the same thing
     *  for KeY ASTs)
     */ 
    private String concatenate(Comment[] comments) {
        if(comments.length == 0) {
            return "";
        }        
        StringBuffer sb = new StringBuffer(comments[0].getText());
        
        for(int i = 1; i < comments.length; i++) {
            Position relativePos = comments[i].getRelativePosition();
            for(int j = 0; j < relativePos.getLine(); j++) {
                sb.append("\n");
            }
            for(int j = 0; j < relativePos.getColumn(); j++) {
                sb.append(" ");
            }
            sb.append(comments[i].getText());
        }
        
        return sb.toString();
    }
    
    
    /**
     * Prepends the Java (i.e., non-JML) modifiers from the passed list
     * to the passed PositionedString. Inserts whitespace in place of 
     * the JML modifiers (in order to preserve position information).
     */
    private PositionedString prependJavaMods(ListOfString mods,
                                             PositionedString ps) {
        StringBuffer sb = new StringBuffer();
        for(String mod : mods) {
            if(javaMods.contains(mod)) {
                sb.append(mod);
            } else {
                sb.append(mod.replaceAll(".", " "));
            }
            sb.append(" ");
        }
        
        int column = ps.pos.getColumn() - sb.toString().length();
        if(column < 0) {
            column = 0;
        }
        de.uka.ilkd.key.java.Position pos 
            = new de.uka.ilkd.key.java.Position(ps.pos.getLine(), column);
        
        return new PositionedString(sb.toString() + ps.text, ps.fileName, pos);
    }
    
    
    /**
     * Puts the JML modifiers from the passed list into a string enclosed
     * in JML markers.
     */
    private String getJMLModString(ListOfString mods) {
        StringBuffer sb = new StringBuffer("/*@");
        
        for(String mod : mods) {
            if(!javaMods.contains(mod)) {
                sb.append(mod + " ");
            }
        }
        
        sb.append("@*/");
        return sb.toString();
    }
    
    
    /**
     * Recursively adds the passed position to the starting positions of 
     * the passed program element and its children.
     */
    private void updatePositionInformation(
                                ProgramElement pe, 
                                de.uka.ilkd.key.java.Position pos) {
        //set start pos
        Position oldPos = pe.getStartPosition();
        Position newPos = new Position(pos.getLine() + oldPos.getLine() - 1, 
                                       pos.getColumn() + oldPos.getColumn() -1);
        pe.setStartPosition(newPos);
        
        //recurse to children
        if(pe instanceof NonTerminalProgramElement) {
            NonTerminalProgramElement ntpe = (NonTerminalProgramElement) pe;
            for(int i = 0; i < ntpe.getChildCount(); i++) {
                updatePositionInformation(ntpe.getChildAt(i), pos);
            }
        }
    }
    
    
    /**
     * Returns the children of the passed program element.
     */
    private ProgramElement[] getChildren(ProgramElement pe) {
        ProgramElement[] result;
        
        if(pe instanceof NonTerminalProgramElement) {
            NonTerminalProgramElement ntpe = (NonTerminalProgramElement) pe;
            int childCount = ntpe.getChildCount();
            result = new ProgramElement[childCount];
            for(int i = 0; i < childCount; i++) {
                result[i] = ntpe.getChildAt(i);
            }
        } else {
            result = new ProgramElement[0];
        }
        
        return result;
    }
    
    
    private Comment[] getCommentsAndSetParent(ProgramElement pe) {
        assert pe != null;
        if(pe.getComments() == null) {
            return new Comment[0];
        }
        
        Comment[] result = pe.getComments().toArray(new Comment[0]);
        for (int i = 0; i < result.length; i++) {
            result[i].setParent(pe);
        }

        return result;
    }
    
    
    
    //-------------------------------------------------------------------------
    //private transformation methods
    //-------------------------------------------------------------------------
    
    private void transformFieldDecl(TextualJMLFieldDecl decl, 
                                    Comment[] originalComments) 
                                                throws SLTranslationException {
        assert originalComments.length > 0;
        
        //prepend Java modifiers
        PositionedString declWithMods = prependJavaMods(decl.getMods(), 
                                                        decl.getDecl());
        
        //only handle ghost fields
        //(model fields are handled later in JMLSpecExtractor)
        if(!decl.getMods().contains("ghost")) {
            if(decl.getMods().contains("model")) {
                return;
            } else {
                throw new SLTranslationException(
                            "JML field declaration has to be ghost or model!", 
                            declWithMods.fileName, 
                            declWithMods.pos);            
            }
        }
        
        //determine parent, child index
        NonTerminalProgramElement astParent
            = originalComments[0].getParent().getASTParent();
        int childIndex
            = astParent.getIndexOfChild(originalComments[0].getParent());
        
        //parse declaration, attach to AST
        Declaration ghostDecl;
        try {
            if(astParent instanceof TypeDeclaration) {
                ghostDecl 
                    = services.getProgramFactory()
                              .parseFieldDeclaration(declWithMods.text);
                updatePositionInformation(ghostDecl, declWithMods.pos);
                
                //set comments: the original list of comments with the declaration, 
                //and the JML modifiers
                ASTList<Comment> newComments 
                   = new ASTArrayList<Comment>(Arrays.asList(originalComments));
                Comment jmlComment = new Comment(getJMLModString(decl.getMods()));
                jmlComment.setParent(ghostDecl);
                newComments.add(jmlComment);
                ghostDecl.setComments(newComments);
                
                attach((FieldDeclaration)ghostDecl, 
                       (TypeDeclaration) astParent, 
                       0);   //No matter what the javadoc for attach() may say, 
                             //this value is *not* used as a child index but as 
                             //an index into astParent.getMembers(), which only 
                             //contains some of the children, not all. 0 is 
                             //topmost position, which should be a safe choice
                             //in any case.
            } else {
                assert astParent instanceof StatementBlock;
                List<Statement> declStatement = services.getProgramFactory()
                          .parseStatements(declWithMods.text);
                assert declStatement.size() == 1;
                ghostDecl 
                    = (LocalVariableDeclaration) declStatement.get(0);
                updatePositionInformation(ghostDecl, declWithMods.pos);
                attach((LocalVariableDeclaration)ghostDecl, 
                       (StatementBlock) astParent, 
                       childIndex); //Unlike above, here the value is really a 
                                    //child index, and here the position really
                                    //matters. 
            }
        } catch(Throwable e) {
            throw new SLTranslationException(e.getMessage()
                                             + " (" 
                                             + e.getClass().getName() 
                                             + ")",                                              
                                             declWithMods.fileName, 
                                             declWithMods.pos,
                                             e.getStackTrace());
        }

        //add ghost modifier
        ASTList<DeclarationSpecifier> mods = ghostDecl.getDeclarationSpecifiers();
        mods.add(new Ghost());
        ghostDecl.setDeclarationSpecifiers(mods);
    }
    

    private void transformMethodDecl(TextualJMLMethodDecl decl, 
                                     Comment[] originalComments) 
                                                throws SLTranslationException {
        assert originalComments.length > 0;
        
        //prepend Java modifiers
        PositionedString declWithMods = prependJavaMods(decl.getMods(), 
                                                        decl.getDecl());
        
        //only handle model methods
        if(!decl.getMods().contains("model")) {
            throw new SLTranslationException(
                                "JML method declaration has to be model!", 
                                declWithMods.fileName, 
                                declWithMods.pos);            
        }
        
        //determine parent
        TypeDeclaration astParent
            = (TypeDeclaration) originalComments[0].getParent().getASTParent();
        
        //parse declaration, attach to AST
        MethodDeclaration methodDecl;
        try {
            methodDecl = services.getProgramFactory()
                                 .parseMethodDeclaration(declWithMods.text);
            updatePositionInformation(methodDecl, declWithMods.pos);
            attach(methodDecl, astParent, 0); //about the 0 see the comment in 
                                              //transformFieldDecl() above
        } catch(Throwable e) {
            throw new SLTranslationException(e.getMessage()
                                             + " (" 
                                             + e.getClass().getName() 
                                             + ")",       
                                             declWithMods.fileName, 
                                             declWithMods.pos,
                                             e.getStackTrace());
        }
        
        //add model modifier
        ASTList<DeclarationSpecifier> mods 
            = methodDecl.getDeclarationSpecifiers();
        mods.add(new Model());
        methodDecl.setDeclarationSpecifiers(mods);
        
        //set comments: the original list of comments with the declaration, 
        //and the JML modifiers
        ASTList<Comment> newComments 
            = new ASTArrayList<Comment>(Arrays.asList(originalComments));
        Comment jmlComment = new Comment(getJMLModString(decl.getMods()));
        jmlComment.setParent(methodDecl);
        newComments.add(jmlComment);
        methodDecl.setComments(newComments);
    }
    
    
    private void transformSetStatement(TextualJMLSetStatement stat,
                                       Comment[] originalComments) 
                                                throws SLTranslationException {
        assert originalComments.length > 0;
        
        //determine parent, child index
        StatementBlock astParent
            = (StatementBlock) originalComments[0].getParent().getASTParent();
        int childIndex 
            = astParent.getIndexOfChild(originalComments[0].getParent());
        
        //parse statement, attach to AST
        try {
            List<Statement> stmtList = services.getProgramFactory()
                      .parseStatements(stat.getAssignment().text);
            assert stmtList.size() == 1;
            CopyAssignment assignStmt 
                = (CopyAssignment) stmtList.get(0);
            SetAssignment setStmt = new SetAssignment(assignStmt);
            updatePositionInformation(setStmt, stat.getAssignment().pos);
            attach(setStmt, astParent, childIndex);
        } catch(Throwable e) {
            throw new SLTranslationException(e.getMessage()
                                             + " (" 
                                             + e.getClass().getName() 
                                             + ")",       
                                             stat.getAssignment().fileName, 
                                             stat.getAssignment().pos,
                                             e.getStackTrace());
        }
    }
    
        
    private void transformClasslevelComments(TypeDeclaration td, 
                                             String fileName) 
            throws SLTranslationException {
        //iterate over all pre-existing children
        ProgramElement[] children = getChildren(td);
        for(int i = 0; i <= children.length; i++) {
            //collect comments 
            //(last position are comments of type declaration itself)
            Comment[] comments = null;
            if(i < children.length) {
                comments = getCommentsAndSetParent(children[i]);
            } else if(td.getComments() != null) {
                assert i > 0; //otherwise there wouldn't even be implicit fields
                comments = td.getComments().toArray(new Comment[0]);
                for(Comment c : comments) {
                    c.setParent(children[i-1]);
                }
            }      
            if(comments == null || comments.length == 0) {
                continue;
            }
            
            //concatenate comments of child, determine position           
            String concatenatedComment = concatenate(comments);
            Position recoderPos = comments[0].getStartPosition();
            de.uka.ilkd.key.java.Position pos 
                = new de.uka.ilkd.key.java.Position(recoderPos.getLine(), 
                                                    recoderPos.getColumn());
                        
            //call preparser            
            KeYJMLPreParser preParser 
                = new KeYJMLPreParser(concatenatedComment, fileName, pos);
            ListOfTextualJMLConstruct constructs 
                = preParser.parseClasslevelComment();
            warnings = warnings.union(preParser.getWarnings());
            
            //handle model and ghost declarations in textual constructs
            //(and set assignments which RecodeR evilly left hanging *behind* 
            //the method to which they belong)
            for(TextualJMLConstruct c : constructs) {
                if(c instanceof TextualJMLFieldDecl) {
                    transformFieldDecl((TextualJMLFieldDecl)c, comments);
                } else if(c instanceof TextualJMLMethodDecl) {
                    transformMethodDecl((TextualJMLMethodDecl)c, comments);
                } else if(c instanceof TextualJMLSetStatement) {
                    if(i == 0 || !(children[i-1] instanceof MethodDeclaration)) {
                        throw new SLTranslationException(
                       "A set assignment only allowed inside of a method body.", 
                       fileName, 
                        pos);
                    }
                    Statement emptyStmt = new EmptyStatement();
                    Comment emptyStmtComment = new Comment();
                    emptyStmtComment.setParent(emptyStmt);
                    StatementBlock methodBody 
                        = ((MethodDeclaration) children[i-1]).getBody();
                    attach(emptyStmt, methodBody, methodBody.getChildCount());
                    transformSetStatement((TextualJMLSetStatement)c, 
                                          new Comment[]{emptyStmtComment}); 
                }
            }
        }
    }
    
    
    private void transformMethodlevelCommentsHelper(ProgramElement pe,
                                                    String fileName) 
                                                throws SLTranslationException {
        //recurse to all pre-existing children
        ProgramElement[] children = getChildren(pe);
        for(int i = 0; i < children.length; i++) {
            transformMethodlevelCommentsHelper(children[i], fileName);
        }
        
        if(pe instanceof MethodDeclaration) return;

        //get comments
        Comment[] comments = getCommentsAndSetParent(pe);
        if(comments.length == 0) {
            return;
        }
        
        //concatenate comments, determine position
        String concatenatedComment = concatenate(comments);
        Position recoderPos = comments[0].getStartPosition();
        de.uka.ilkd.key.java.Position pos 
            = new de.uka.ilkd.key.java.Position(recoderPos.getLine(), 
                                                recoderPos.getColumn());

        //call preparser
        KeYJMLPreParser preParser 
            = new KeYJMLPreParser(concatenatedComment, fileName, pos);
        ListOfTextualJMLConstruct constructs 
            = preParser.parseMethodlevelComment();
        warnings = warnings.union(preParser.getWarnings());

        //handle ghost declarations and set assignments in textual constructs
        for(TextualJMLConstruct c : constructs) {
            if(c instanceof TextualJMLFieldDecl) {
                transformFieldDecl((TextualJMLFieldDecl)c, comments);
            } else if(c instanceof TextualJMLSetStatement) {
                transformSetStatement((TextualJMLSetStatement)c, comments);
            }
        }
    }
    
    
    private void transformMethodlevelComments(MethodDeclaration md,
                                              String fileName) 
                                                throws SLTranslationException {
        StatementBlock body = md.getBody();
        if(body != null) {
            transformMethodlevelCommentsHelper(body, fileName);            
        }
    }

    
    
    //-------------------------------------------------------------------------
    //RecoderModelTransformer - abstract methods implementation
    //-------------------------------------------------------------------------

    protected void makeExplicit(TypeDeclaration td) {
        assert false;
    }
    
    
    public void makeExplicit() {
        //abort if JML is disabled
        if(!ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().useJML()) {
            return;
        }

        try {
            //iterate over all compilation units
            for(int i = 0, m = getUnits().size(); i < m; i++) {
                CompilationUnit unit = getUnits().get(i);
                
                //copy comments of compilation unit to primary type declaration
                if(unit.getComments() != null 
                        && unit.getTypeDeclarationCount() > 0) {
                    TypeDeclaration td = unit.getPrimaryTypeDeclaration();
                    ASTList<Comment> tdComments = new ASTArrayList<Comment>(); 
                    tdComments.addAll(unit.getComments().deepClone());
                    td.setComments(tdComments);
                }
                
                //iterate over all type declarations of the compilation unit
                TypeDeclarationCollector tdc = new TypeDeclarationCollector();
                tdc.walk(unit);
                HashSet<TypeDeclaration> typeDeclarations = tdc.result();               
                for(TypeDeclaration td : typeDeclarations) {                    
                    //collect pre-existing operations
                    List<? extends Constructor> constructorList 
                        = td.getConstructors();
                    List<Method> methodList = td.getMethods();
                    
                    // fix mu: units carry an artificial file name.
                    // use getOriginalDataLocation instead
                    DataLocation dl = unit.getOriginalDataLocation();
                    String fileName = dl == null ? "" : dl.toString();
                    fileName = fileName.replaceFirst("FILE:", "");
                    
                    transformClasslevelComments(td, fileName);
                    
                    //iterate over all pre-existing constructors
                    for(int k = 0, o = constructorList.size(); k < o; k++) {
                        if(constructorList.get(k) 
                           instanceof ConstructorDeclaration) {
                            ConstructorDeclaration cd 
                                = (ConstructorDeclaration) 
                                   constructorList.get(k);
                            transformMethodlevelComments(cd, fileName);
                        }
                    }               
                                        
                    //iterate over all pre-existing methods
                    for(int k = 0, o = methodList.size(); k < o; k++) {
                        if(methodList.get(k) instanceof MethodDeclaration) { // might be ImplicitEnumMethod
                            MethodDeclaration md 
                                = (MethodDeclaration) 
                                   methodList.get(k);
                            transformMethodlevelComments(md, fileName);
                        }
                    }               
                    
                    td.makeAllParentRolesValid();
                }
            }
        } catch(SLTranslationException e) {
            RuntimeException runtimeE 
            	= new RuntimeException(e.getMessage() 
            		               + "\n" + e.getFileName() 
            		               + ", line " + e.getLine()
            		               + ", column " + e.getColumn());
            runtimeE.setStackTrace(e.getStackTrace());
            throw runtimeE;
        }
    }
    
    
    public static SetOfPositionedString getWarningsOfLastInstance() {
        return warnings;
    }
    
    
    //-------------------------------------------------------------------------
    //inner classes
    //-------------------------------------------------------------------------
    
    private static class TypeDeclarationCollector extends SourceVisitor{
        
        HashSet<TypeDeclaration> result = new HashSet<TypeDeclaration>();
                
        public void walk(SourceElement s){
            s.accept(this);
            if(s instanceof NonTerminalProgramElement){
                NonTerminalProgramElement pe = (NonTerminalProgramElement) s;
                for(int i=0; i<pe.getChildCount(); i++){
                    walk(pe.getChildAt(i));
                }
            }
        }
        
        public void visitClassDeclaration(ClassDeclaration td){
            result.add(td);
            super.visitClassDeclaration(td);
        }
        
        public void visitInterfaceDeclaration(InterfaceDeclaration td) {
            result.add(td);
            super.visitInterfaceDeclaration(td);
        }
               
        public HashSet<TypeDeclaration> result(){           
            return result;
        }
    }
}
