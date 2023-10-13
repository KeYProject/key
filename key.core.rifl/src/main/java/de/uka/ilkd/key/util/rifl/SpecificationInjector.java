/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.rifl;

import java.util.*;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import de.uka.ilkd.key.util.rifl.SpecificationEntity.Type;

import recoder.abstraction.ClassType;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.SourceInfo;

/**
 * Writes JML* translation of RIFL specifications to Java files. This is a manipulating Recoder
 * source visitor. Implementation warning: manipulating the AST before traversing it may have
 * unexpected results.
 *
 * @author bruns
 */
public class SpecificationInjector extends SourceVisitor {

    private static final String LINE_BREAK = "\n";
    private static final String DEFAULT_SPEC_COMMENT =
        LINE_BREAK + "// JML* comment created by KeY RIFL Transformer." + LINE_BREAK;

    /**
     * Produces JML* respects clauses. Clauses are internally labeled with keys (resulting from
     * security domains in RIFL), which are discarded in the final output.
     *
     * @author bruns
     */
    private static class JMLFactory {

        private static final String DEFAULT_INDENTATION = "  ";
        private static final String DEFAULT_KEY = "low";
        private static final String RESULT = "\\result";
        private static final String DETERMINES = "determines";
        private static final String BY = " \\by";
        private static final String JML_LINE_START = "@ ";
        private static final String JML_END = "@*/" + LINE_BREAK;
        private static final String JML_CLAUSE_END = ";";
        private static final String JML_START = LINE_BREAK + DEFAULT_INDENTATION + "/*@ ";

        private final String indentation;
        private final Map<String, Set<Entry<String, Type>>> respects = new HashMap<>();
        private SpecificationContainer sc;

        JMLFactory(SpecificationContainer sc) {
            indentation = DEFAULT_INDENTATION;
            this.sc = sc;
        }

        @SuppressWarnings("unused")
        JMLFactory(int indent) {
            indentation = " ".repeat(indent);
        }

        @SuppressWarnings("unused")
        void addResultToDetermines(Type t) {
            put(DEFAULT_KEY, t, RESULT);
        }

        // TODO allow more respects clauses

        /**
         * Adds \result to a determines clause labeled by key.
         */
        void addResultToDetermines(String key, Type t) {
            put(key, t, RESULT);
        }

        @SuppressWarnings("unused")
        void addToDetermines(String name, Type t) {
            put(DEFAULT_KEY, t, name);
        }

        void addToDetermines(String name, Type t, String key) {
            put(key, t, name);
        }

        String getRespects(String domain, final Type t) {
            return getRespects(respects.get(domain), t);
        }

        String getRespects(Set<String> oneRespect) {
            if (oneRespect != null && !oneRespect.isEmpty()) {
                return String.join(", ", oneRespect);
            } else {
                return " \\nothing";
            }
        }

        String getRespects(Set<Entry<String, Type>> oneRespect, final Type t) {
            var r = oneRespect.stream().filter(p -> p.getValue() == t).map(Entry::getKey)
                    .collect(Collectors.joining(", "));
            if (r.isEmpty()) {
                return " \\nothing";
            }
            return r;
        }

        /**
         * Gets a formatted JML comment.
         */
        String getSpecification() {
            // start JML
            final var sb = new StringBuilder();


            // respects clauses
            for (final Entry<String, Set<Entry<String, Type>>> oneRespect : respects.entrySet()) {
                final String domain = oneRespect.getKey();
                final Set<String> flowsFromDomain = sc.flows(domain);

                Set<String> oneRespects = new LinkedHashSet<>();
                for (final String flowsFrom : flowsFromDomain) {
                    final Set<Entry<String, Type>> es = respects.get(flowsFrom);
                    if (es != null) { // sources
                        for (final Entry<String, Type> e : es) {
                            if (e.getValue() == Type.SOURCE) {
                                oneRespects.add(e.getKey());
                            }
                        }
                    }
                }
                final Set<Entry<String, Type>> es = respects.get(domain);
                if (es != null) { // sources
                    for (final Entry<String, Type> reflFlow : es) {
                        if (reflFlow.getValue() == Type.SOURCE) {
                            oneRespects.add(reflFlow.getKey());
                        }
                    }
                }

                sb.append(indentation);
                sb.append(DEFAULT_INDENTATION);
                sb.append(JML_LINE_START);
                sb.append(DETERMINES);
                sb.append(getRespects(domain, Type.SINK)); // sinks
                sb.append(BY);
                sb.append(getRespects(oneRespects));
                sb.append(JML_CLAUSE_END);
                sb.append(LINE_BREAK);
            }

            if (!sb.toString().trim().isEmpty()) {
                sb.insert(0, indentation + JML_START + LINE_BREAK);
                // close JML
                sb.append(indentation);
                sb.append(DEFAULT_INDENTATION);
                sb.append(JML_END);
                return sb.toString();
            } else {
                return null;
            }


        }

        private void put(String key, Entry<String, Type> value) {
            if (key == null) {
                return;
            }
            Set<Entry<String, Type>> target = respects.get(key);
            if (target == null) {
                target = new LinkedHashSet<>();
            }
            target.add(value);
            respects.put(key, target);
        }

        private void put(String key, Type t, String value) {
            put(key, new AbstractMap.SimpleEntry<>(value, t));
        }
    } // private class end


    private final SpecificationContainer sc;
    private final SourceInfo si;

    private final List<MethodDeclaration> specifiedMethodDeclarations;

    public SpecificationInjector(SpecificationContainer sc, SourceInfo sourceInfo) {
        this.sc = sc;
        si = sourceInfo;
        specifiedMethodDeclarations = new LinkedList<>();
    }

    public List<MethodDeclaration> getSpecifiedMethodDeclarations() {
        return specifiedMethodDeclarations;
    }

    // ////////////////////////////////////////////////////////////
    // private methods
    // ////////////////////////////////////////////////////////////

    private void accessChildren(JavaNonTerminalProgramElement pe) {
        for (int i = 0; i < pe.getChildCount(); i++) {
            pe.getChildAt(i).accept(this);
        }
    }

    private void addComment(JavaProgramElement se, String comment) {
        // remember which methods were specified and generate po files only for them
        if (se instanceof MethodDeclaration) {
            specifiedMethodDeclarations.add((MethodDeclaration) se);
        }

        // fixes issue with Recoder that it writes comments _after_ the element
        final NonTerminalProgramElement parent = se.getASTParent();
        assert parent != null : "Program element " + se + " with null parent";
        for (int i = 0; i < parent.getChildCount(); i++) {
            if (i > 0 && parent.getChildAt(i) == se) {
                // chose previous element
                se = (JavaProgramElement) parent.getChildAt(i - 1);
            } // TODO: what if se is the 0th child ??
        }

        final ASTArrayList<Comment> commentList = new ASTArrayList<>();
        final ASTList<Comment> oldComments = se.getComments();
        if (oldComments != null) {
            commentList.addAll(oldComments);
        }
        if (comment != null && !comment.isEmpty()) {
            commentList.add(new Comment(comment));
        }
        se.setComments(commentList);
    }

    // ////////////////////////////////////////////////////////////
    // visitor methods
    // ////////////////////////////////////////////////////////////

    @Override
    public void visitClassDeclaration(ClassDeclaration cd) {
        cd.setProgramModelInfo(si);
        accessChildren(cd);
        addComment(cd, DEFAULT_SPEC_COMMENT);
    }


    @Override
    public void visitCompilationUnit(CompilationUnit cu) {
        accessChildren(cu);
    }

    @Override
    public void visitInterfaceDeclaration(InterfaceDeclaration id) {
        id.setProgramModelInfo(si);
        accessChildren(id);
        addComment(id, DEFAULT_SPEC_COMMENT);
    }

    @Override
    public void visitMethodDeclaration(MethodDeclaration md) {
        md.setProgramModelInfo(si);
        final JMLFactory factory = new JMLFactory(sc);

        // add return value
        final String returnDomainSrc = sc.returnValue(md, Type.SOURCE);
        factory.addResultToDetermines(returnDomainSrc, Type.SOURCE);
        final String returnDomainSnk = sc.returnValue(md, Type.SINK);
        factory.addResultToDetermines(returnDomainSnk, Type.SINK);

        // add parameters
        for (int i = 0; i < md.getParameterDeclarationCount(); i++) {
            final ParameterDeclaration pd = md.getParameterDeclarationAt(i);
            final String paraName = pd.getVariableSpecification().getName();
            final String paramSrc = sc.parameter(md, i + 1, Type.SOURCE);
            final String paramSnk = sc.parameter(md, i + 1, Type.SINK);
            factory.addToDetermines(paraName, Type.SOURCE, paramSrc);
            factory.addToDetermines(paraName, Type.SINK, paramSnk);
        }

        // add fields
        final ClassType ct = md.getContainingClassType();
        final String pkg = ct.getPackage().getFullName();
        final String cls = ct.getName();
        for (int i = 0; i < md.getASTParent().getChildCount(); i++) {
            final JavaProgramElement fd = (JavaProgramElement) md.getASTParent().getChildAt(i);
            if (fd instanceof FieldDeclaration) {
                final String field = ((FieldDeclaration) fd).getVariables().get(0).getName();
                final String fName = cls + "." + field;
                final String fieldSrc = sc.field(pkg, cls, field, Type.SOURCE);
                final String fieldSnk = sc.field(pkg, cls, field, Type.SINK);
                factory.addToDetermines(fName, Type.SOURCE, fieldSrc);
                factory.addToDetermines(fName, Type.SINK, fieldSnk);
            }
        }
        // only add comment for methods for which we generated a specification
        String comment = factory.getSpecification();
        if (comment != null) {
            addComment(md, factory.getSpecification());
        }
    }
}
