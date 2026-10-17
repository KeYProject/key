/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.jvm.profile;

import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.rule.BuiltInRule;

import org.key_project.jvm.rule.GotoRestoreRule;
import org.key_project.jvm.rule.GotoSpliceRule;
import org.key_project.jvm.rule.IfLiteralRule;
import org.key_project.util.collection.ImmutableList;

/**
 * The Java DL profile for bytecode verification. It extends the plain {@link JavaProfile} and
 * appends the few built-in rules that implement JVM {@code goto} (and the constant-condition
 * wrappers the transpiler emits for reachability and label guards).
 * <p>
 * The additional rules are <em>appended at the tail</em>: {@link JavaProfile#initBuiltInRules()}
 * guarantees that {@link de.uka.ilkd.key.rule.UseOperationContractRule} stays the first element
 * (the proof management machinery relies on that), so we must never prepend.
 *
 * @see GotoSpliceRule
 * @see GotoRestoreRule
 * @see IfLiteralRule
 */
public class JvmProfile extends JavaProfile {

    /** The identifier used to select this profile (cf. {@code ProofInitServiceUtil}). */
    public static final String PROFILE_ID = "java-jvm";

    public static final String DISPLAY_NAME = "Java + JVM Bytecode Profile";

    /** The singleton instance, reused by the {@link JvmProfileResolver}. */
    public static final JvmProfile INSTANCE = new JvmProfile();

    @Override
    protected ImmutableList<BuiltInRule> initBuiltInRules() {
        // super keeps UseOperationContractRule first; append our rules at the tail.
        return super.initBuiltInRules()
                .append(GotoSpliceRule.INSTANCE)
                .append(GotoRestoreRule.INSTANCE)
                .append(IfLiteralRule.INSTANCE);
    }

    @Override
    public String ident() {
        return PROFILE_ID;
    }

    @Override
    public String displayName() {
        return DISPLAY_NAME;
    }

    @Override
    public String description() {
        return "A profile for verifying compiled Java (bytecode) by transpilation: " +
            "lifts .class/.jar to Java over the jvm.Local runtime and handles unstructured " +
            "goto with the JVM built-in rules.";
    }
}
