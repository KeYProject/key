/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.transformations.pipeline.lambda;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import com.github.javaparser.ast.DataKey;
import com.github.javaparser.ast.jml.doc.JmlDoc;
import com.github.javaparser.ast.jml.doc.JmlDocStmt;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;
import org.jspecify.annotations.Nullable;

/**
 * The (explicit) JML contract of a lambda expression or of a method reference, in the form of
 * the specification clauses written inside the lambda's block body (Csiky, Def. 6):
 * <pre>
 * (x) -&gt; {
 *     //@ requires pre;
 *     //@ ensures post;
 *     //@ invariant inv;
 *     //@ assignable footprint;
 *     //@ accessible acc;
 *     ...
 * }
 * </pre>
 * <p>
 * The clauses are extracted by the {@link LambdaReplacer} (as leading {@link JmlDocStmt}
 * statements of the block body), stored on the generated class declaration via the {@link #KEY}
 * data key, and later turned into JML model methods (and {@code represents} clauses) by the
 * {@code LambdaContractModelMethods} pipeline step — the "contract conversion" of Csiky's
 * thesis, Def. 7/8.
 * <p>
 * Only clause kinds that {@link ClauseKind} knows about are captured; every other JML comment
 * inside a lambda body is left untouched.
 *
 * @author weigl
 */
public final class LambdaContractSpec {

    /** Data key under which the contract is attached to the generated (local) class. */
    public static final DataKey<LambdaContractSpec> KEY = new DataKey<>() {
    };

    /**
     * The specification clause kinds of a lambda contract, mapping to the model methods of
     * Table 6.1 of the thesis.
     */
    public enum ClauseKind {
        REQUIRES, ENSURES, INVARIANT, ASSIGNABLE, ACCESSIBLE;

        /**
         * The model method a clause of this kind is converted into (Table 6.1). {@code null}
         * marks kinds without a model method (the frame clauses can also be stated as model
         * fields).
         */
        @Nullable
        String modelMethodName() {
            return switch (this) {
                case REQUIRES -> "preCondition";
                case ENSURES -> "postCondition";
                case INVARIANT -> "invariantMethod";
                case ASSIGNABLE -> "frameCondition";
                case ACCESSIBLE -> "accessibleMethod";
            };
        }

        /** The model field a frame clause can alternatively be converted into. */
        @Nullable
        String modelFieldName() {
            return switch (this) {
                case ASSIGNABLE -> "footprint";
                case ACCESSIBLE -> "accessibleFields";
                default -> null;
            };
        }

        /**
         * Whether the generated model method additionally gets a parameter {@code __result}
         * holding the result of the functional method (Def. 7: postCondition and
         * invariantMethod).
         */
        boolean takesResult() {
            return this == ENSURES || this == INVARIANT;
        }

        static @Nullable ClauseKind fromKeyword(String keyword) {
            return switch (keyword.toLowerCase(Locale.ROOT)) {
                case "requires" -> REQUIRES;
                case "ensures" -> ENSURES;
                case "invariant" -> INVARIANT;
                case "assignable", "modifies" -> ASSIGNABLE;
                case "accessible" -> ACCESSIBLE;
                default -> null;
            };
        }
    }

    /** A single specification clause: its kind and the raw JML expression text. */
    public record Clause(ClauseKind kind, String expression) {
    }

    private final List<Clause> clauses = new ArrayList<>();

    public void add(Clause clause) {
        clauses.add(clause);
    }

    public void addAll(LambdaContractSpec other) {
        if (other != null) {
            clauses.addAll(other.clauses);
        }
    }

    public List<Clause> clauses() {
        return clauses;
    }

    /**
     * Extracts the leading contract clauses of the given block body and (optionally) removes
     * the consumed {@link JmlDocStmt} statements from the block.
     *
     * @param block the block body of a lambda expression or of the target method of a method
     *        reference
     * @param remove whether to remove the consumed JML statements from {@code block} (safe only
     *        for cloned bodies, e.g. the SAM method body of a generated class)
     * @return the extracted contract, or {@code null} if the body starts with no JML
     *         specification clauses
     */
    public static @Nullable LambdaContractSpec extract(BlockStmt block, boolean remove) {
        List<JmlDoc> docs = new ArrayList<>();
        // Iterate over a snapshot: removing JML statements from the block during iteration
        // over the live NodeList would throw a ConcurrentModificationException.
        List<Statement> stmts = new ArrayList<>(block.getStatements());
        for (Statement stmt : stmts) {
            if (!(stmt instanceof JmlDocStmt jml)) {
                break;
            }
            docs.addAll(jml.getJmlComments());
            if (remove) {
                stmt.remove();
            }
        }
        return fromJmlDocs(docs);
    }

    /**
     * Extracts the specification clauses written in the given JML comments (e.g. the leading
     * {@link JmlDocStmt} of a lambda body, or the class-level JML comments preceding the target
     * method of a method reference). Returns {@code null} if the comments contain no clauses.
     */
    public static @Nullable LambdaContractSpec fromJmlDocs(List<JmlDoc> docs) {
        if (docs.isEmpty()) {
            return null;
        }
        LambdaContractSpec spec = new LambdaContractSpec();
        for (JmlDoc doc : docs) {
            for (String line : normalize(doc.getContent())) {
                Clause c = clauseOf(line);
                if (c != null) {
                    spec.add(c);
                }
            }
        }
        return spec.clauses.isEmpty() ? null : spec;
    }

    /**
     * Rewrites the identifiers of all clause bodies with the given name mapping. Used to
     * rename the parameters of a method reference target to the parameter names of the
     * synthetic lambda expression (Def. 8, "Application: Method References").
     */
    public void renameIdentifiers(java.util.Map<String, String> rename) {
        if (rename.isEmpty()) {
            return;
        }
        for (int i = 0; i < clauses.size(); i++) {
            Clause c = clauses.get(i);
            String expr = ClauseText.rewrite(c.expression(), rename::get);
            if (!expr.equals(c.expression())) {
                clauses.set(i, new Clause(c.kind(), expr));
            }
        }
    }

    /**
     * Strips the JML comment markers ({@code //@}, {@code /*@ ... @*}{@code /} and the line
     * leaders {@code @}) from the content of a single JML comment, resulting in one text line
     * per JML entity.
     */
    private static List<String> normalize(String content) {
        String s = content.replace("/*@", "").replace("*/", "");
        List<String> lines = new ArrayList<>();
        for (String line : s.split("\\r?\\n")) {
            String t = line.trim();
            if (t.startsWith("//@")) {
                t = t.substring(3).trim();
            } else if (t.startsWith("@")) {
                t = t.substring(1).trim();
            }
            if (!t.isEmpty()) {
                lines.add(t);
            }
        }
        return lines;
    }

    /**
     * Splits a normalized JML line {@code keyword expression;} into a clause. {@code null} for
     * lines that are no specification clause (e.g. {@code set} assignments or plain comments).
     */
    private static @Nullable Clause clauseOf(String line) {
        String[] parts = line.split("\\s+", 2);
        if (parts.length != 2) {
            return null;
        }
        ClauseKind kind = ClauseKind.fromKeyword(parts[0]);
        if (kind == null) {
            return null;
        }
        String expr = parts[1].trim();
        while (expr.endsWith(";")) {
            expr = expr.substring(0, expr.length() - 1).trim();
        }
        return expr.isEmpty() ? null : new Clause(kind, expr);
    }
}
