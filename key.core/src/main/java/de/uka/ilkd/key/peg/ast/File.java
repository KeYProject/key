/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;

/**
 * Represents the root of a KeY specification file.
 * Corresponds to the grammar rule: file: DOC_COMMENT* (profile? preferences? decls problem? proof?) EOF;
 *
 * @author Cline
 * @version 1.0
 */
@NullMarked
public class File extends BaseAstNode {
    private final List<String> docComments;
    private final @Nullable Profile profile;
    private final @Nullable Preferences preferences;
    private final DeclList decls;
    private final @Nullable Problem problem;
    private final @Nullable Proof proof;

    public File(Position position,
                List<String> docComments, @Nullable Profile profile,
                @Nullable Preferences preferences, DeclList decls,
                @Nullable Problem problem, @Nullable Proof proof) {
        super(position);
        this.docComments = docComments;
        this.profile = profile;
        this.preferences = preferences;
        this.decls = decls;
        this.problem = problem;
        this.proof = proof;
        
        setChildParent(profile);
        setChildParent(preferences);
        setChildParent(decls);
        setChildParent(problem);
        setChildParent(proof);
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public List<String> getDocComments() {
        return docComments;
    }

    public @Nullable Profile getProfile() {
        return profile;
    }

    public @Nullable Preferences getPreferences() {
        return preferences;
    }

    public DeclList getDecls() {
        return decls;
    }

    public @Nullable Problem getProblem() {
        return problem;
    }

    public @Nullable Proof getProof() {
        return proof;
    }
}