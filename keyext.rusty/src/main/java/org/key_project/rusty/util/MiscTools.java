/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.util;

import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.expr.AssignmentExpression;
import org.key_project.rusty.ast.expr.CompoundAssignmentExpression;
import org.key_project.rusty.ast.pat.BindingPattern;
import org.key_project.rusty.ast.visitor.RustyASTVisitor;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

public final class MiscTools {
    /**
     * All variables read in the specified program element, excluding newly declared variables.
     *
     * @param pe a program element.
     * @param services services.
     * @return all variables read in the specified program element, excluding newly declared
     *         variables.
     */
    public static ImmutableSet<ProgramVariable> getLocalIns(RustyProgramElement pe,
            Services services) {
        final var rpvc = new ReadPVCollector(pe, services);
        rpvc.start();
        return rpvc.result();
    }

    /**
     * All variables changed in the specified program element, excluding newly declared variables.
     *
     * @param pe a program element.
     * @param services services.
     * @return all variables changed in the specified program element, excluding newly declared
     *         variables.
     */
    public static ImmutableSet<ProgramVariable> getLocalOuts(RustyProgramElement pe,
            Services services) {
        final WrittenAndDeclaredPVCollector wpvc = new WrittenAndDeclaredPVCollector(pe, services);
        wpvc.start();
        return wpvc.getWrittenPVs();
    }

    // -------------------------------------------------------------------------
    // inner classes
    // -------------------------------------------------------------------------

    private static final class ReadPVCollector extends RustyASTVisitor {
        /**
         * The list of resulting (i.e., read) program variables.
         */
        private ImmutableSet<ProgramVariable> result = DefaultImmutableSet.nil();

        /**
         * The declared program variables.
         */
        private ImmutableSet<ProgramVariable> declaredPVs =
            DefaultImmutableSet.nil();

        public ReadPVCollector(RustyProgramElement root, Services services) {
            super(root, services);
        }

        @Override
        protected void doDefaultAction(RustyProgramElement node) {
            if (node instanceof ProgramVariable pv) {
                if (!declaredPVs.contains(pv)) {
                    result = result.add(pv);
                }
            } else if (node instanceof BindingPattern bp) {
                var pv = bp.pv();
                assert !declaredPVs.contains(pv);
                result = result.remove(pv);
                declaredPVs = declaredPVs.add(pv);
            }
        }

        public ImmutableSet<ProgramVariable> result() {
            return result;
        }
    }

    private static class WrittenAndDeclaredPVCollector extends RustyASTVisitor {
        /**
         * The written program variables.
         */
        private ImmutableSet<ProgramVariable> writtenPVs =
            DefaultImmutableSet.nil();

        /**
         * The declared program variables.
         */
        private ImmutableSet<ProgramVariable> declaredPVs =
            DefaultImmutableSet.nil();

        public WrittenAndDeclaredPVCollector(RustyProgramElement root, Services services) {
            super(root, services);
        }

        @Override
        protected void doDefaultAction(RustyProgramElement node) {
            if (node instanceof AssignmentExpression ae) {
                var lhs = ae.lhs();
                if (lhs instanceof ProgramVariable pv) {
                    if (!declaredPVs.contains(pv)) {
                        writtenPVs = writtenPVs.add(pv);
                    }
                }
            } else if (node instanceof CompoundAssignmentExpression cae) {
                var lhs = cae.left();
                if (lhs instanceof ProgramVariable pv) {
                    if (!declaredPVs.contains(pv)) {
                        writtenPVs = writtenPVs.add(pv);
                    }
                }
            } else if (node instanceof BindingPattern bp) {
                var pv = bp.pv();
                assert !declaredPVs.contains(pv);
                assert !writtenPVs.contains(pv);
                declaredPVs = declaredPVs.add(pv);
            }
        }

        public ImmutableSet<ProgramVariable> getWrittenPVs() {
            return writtenPVs;
        }

        public ImmutableSet<ProgramVariable> getDeclaredPVs() {
            return declaredPVs;
        }
    }
}
