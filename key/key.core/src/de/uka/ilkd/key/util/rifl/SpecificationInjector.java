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

package de.uka.ilkd.key.util.rifl;

import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import recoder.abstraction.ClassType;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.SourceInfo;

/**
 * Writes JML* translation of RIFL specifications to Java files. This is a
 * manipulating Recoder source visitor. Implementation warning: manipulating the
 * AST before traversing it may have unexpected results.
 *
 * @author bruns
 */
public class SpecificationInjector extends SourceVisitor {

    /**
     * Produces JML* respects clauses. Clauses are internally labeled with keys
     * (resulting from security domains in RIFL), which are discarded in the
     * final output.
     *
     * @author bruns
     */
    private static class JMLFactory {

        private static final String DEFAULT_INDENTATION = "  ";
        private static final String DEFAULT_KEY = "low";
        private static final String RESULT = "\\result";
        private static final String DETERMINES = "determines";
        private static final String JML_END = "@*/\n";
        private static final String JML_START = "\n"+DEFAULT_INDENTATION+"/*@ ";

        private final String indentation;
        private final Map<String, Set<String>> respects = new HashMap<String, Set<String>>();
        private SpecificationContainer sc;
        JMLFactory(SpecificationContainer sc) {
            indentation = DEFAULT_INDENTATION;
            this.sc = sc;
        }

        @SuppressWarnings("unused")
        JMLFactory(int indent) {
            final StringBuffer sb = new StringBuffer();
            for (int i = 0; i < indent; i++)
                sb.append(' ');
            indentation = sb.toString();
        }

        @SuppressWarnings("unused")
        void addResultToDetermines() {
            put(DEFAULT_KEY, RESULT);
        }

        // TODO allow more respects clauses

        /** Adds \result to a determines clause labeled by key. */
        void addResultToDetermines(String key) {
            put(key, RESULT);
        }

        @SuppressWarnings("unused")
        void addToDetermines(String name) {
            put(DEFAULT_KEY, name);
        }

        void addToDetermines(String name, String key) {
            put(key, name);
        }

        String getRespects(String domain) {
            return getRespects(respects.get(domain));
        }

        String getRespects(Set<String> oneRespect) {
            String result = "";
            if (oneRespect != null && 0 < oneRespect.size()) {
        		for (final String elem : oneRespect) {
                    result += " "+elem+",";
                }
        		result = result.substring(0,result.length()-1);
        	}
        	return result;
        }

        /** Gets a formatted JML comment. */
        String getSpecification() {
            // start JML
            final StringBuffer sb = new StringBuffer(indentation);
            sb.append(JML_START + "\n");
            // debug
            //System.out.println("Respects: "+respects);

            // respects clauses
            for (final Entry<String, Set<String>> oneRespect : respects.entrySet()) {
                String domain = oneRespect.getKey();
                Set<String> flowsFromDomain = sc.flows(domain);
                // debug
                // System.out.println("flows to "+domain+" "+flowsFromDomain);

            	Set<String> oneRespects = new LinkedHashSet<String>();
                for (final String flowsFrom : flowsFromDomain) {
                    oneRespects.addAll(respects.get(flowsFrom));
            	}
            	oneRespects.addAll(respects.get(domain));

            	sb.append(indentation);
                sb.append(DEFAULT_INDENTATION);
                sb.append("@ ");
                sb.append(DETERMINES);
                sb.append(getRespects(domain));
                sb.append(" \\by ");
                sb.append(getRespects(oneRespects));
                sb.append("; //"+domain+" -> "+flowsFromDomain+"\n");
            }
            // close JML
            sb.append(indentation);
            sb.append(DEFAULT_INDENTATION);
            sb.append(JML_END);
            return sb.toString();
        }

        private void put(String key, String value) {
            if (key == null)
                return;
            Set<String> target = respects.get(key);
            if (target == null) {
                target = new LinkedHashSet<String>();
            }
            target.add(value);
            respects.put(key, target);
        }
    } // private class end


    private final SpecificationContainer sc;
    private final SourceInfo si;

    public SpecificationInjector(SpecificationContainer sc, SourceInfo sourceInfo) {
        this.sc = sc;
        si = sourceInfo;
    }

    // ////////////////////////////////////////////////////////////
    // private methods
    // ////////////////////////////////////////////////////////////

    private void accessChildren(JavaNonTerminalProgramElement pe) {
        for (int i = 0; i < pe.getChildCount(); i++)
            pe.getChildAt(i).accept(this);
    }

    private static void addComment(JavaProgramElement se, String comment) {
        // fixes issue with Recoder that it writes comments _after_ the element
        final NonTerminalProgramElement parent = se.getASTParent();
        assert parent != null : "Program element "+se+" with null parent";
        for (int i = 0; i < parent.getChildCount(); i++) {
            if (i > 0 && parent.getChildAt(i) == se) {
                // chose previous element
                se = (JavaProgramElement) parent.getChildAt(i - 1);
            } // TODO: what if se is the 0th child ??
        }

        final ASTArrayList<Comment> commentList = new ASTArrayList<Comment>();
        final ASTList<Comment> oldComments = se.getComments();
        if (oldComments != null)
            commentList.addAll(oldComments);
        commentList.add(new Comment(comment));
        se.setComments(commentList);
    }

    // ////////////////////////////////////////////////////////////
    // visitor methods
    // ////////////////////////////////////////////////////////////

    @Override
    public void visitClassDeclaration(ClassDeclaration cd) {
        cd.setProgramModelInfo(si);
        accessChildren(cd);
        addComment(cd, "\n// JML* comment created by KeY RIFL Transformer.\n");
    }


    @Override
    public void visitCompilationUnit(CompilationUnit cu) {
        accessChildren(cu);
    }

    @Override
    public void visitInterfaceDeclaration(InterfaceDeclaration id) {
        id.setProgramModelInfo(si);
        accessChildren(id);
        addComment(id, "\n// JML* comment created by KeY RIFL Transformer.\n");
    }

    @Override
    public void visitMethodDeclaration(MethodDeclaration md) {
        md.setProgramModelInfo(si);
        final JMLFactory factory = new JMLFactory(sc);

        // add return value
        final String returnDomain = sc.returnValue(md);
        // debug
        // System.out.println(".... return domain: "+returnDomain);
        factory.addResultToDetermines(returnDomain);

        // add parameters
        for (int i = 0; i < md.getParameterDeclarationCount(); i++) {
            final ParameterDeclaration pd = md.getParameterDeclarationAt(i);
            // debug
            // System.out.println(".... "+ pd.getVariableSpecification().getName() +" domain: " + sc.parameter(md, i+1));
            factory.addToDetermines(pd.getVariableSpecification().getName(), sc.parameter(md, i+1));
        }

        // add fields
        final ClassType ct = md.getContainingClassType();
        final String pkg = ct.getPackage().getFullName();
        final String cls = ct.getName();
        for (int i = 0; i < md.getASTParent().getChildCount(); i++) {
            final JavaProgramElement fd = (JavaProgramElement) md.getASTParent().getChildAt(i);
            if (fd instanceof FieldDeclaration) {
                final String field = ((FieldDeclaration) fd).getVariables().get(0).getName();
                // debug
                // System.out.println(".... "+ field +" domain: " + sc.field(pkg, cls, field));
                factory.addToDetermines(field, sc.field(pkg, cls, field));
            }
        }
        addComment(md, factory.getSpecification());
    }
}