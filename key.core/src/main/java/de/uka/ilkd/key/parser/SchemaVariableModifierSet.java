/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser;


public abstract class SchemaVariableModifierSet {

    private boolean strict = false;
    private boolean rigid = false;
    private boolean list = false;


    public boolean rigid() {
        return rigid;
    }


    protected boolean rigidEnabled() {
        return false;
    }


    public boolean strict() {
        return strict;
    }


    protected boolean strictEnabled() {
        return false;
    }


    public boolean list() {
        return list;
    }


    protected boolean listEnabled() {
        return false;
    }


    /**
     * @return <code>true</code> iff <code>option</code> is a valid modifier for the considered kind
     *         of schema variables
     */
    public boolean addModifier(String option) {
        if ("strict".equals(option)) {
            return addStrict();
        } else if ("rigid".equals(option)) {
            return addRigid();
        } else if ("list".equals(option)) {
            return addList();
        }

        return false;
    }

    public boolean addRigid() {
        this.rigid = true;
        return rigidEnabled();
    }

    public boolean addStrict() {
        this.strict = true;
        return strictEnabled();
    }

    public boolean addList() {
        this.list = true;
        return listEnabled();
    }

    public static class ProgramSV extends SchemaVariableModifierSet {
        protected boolean listEnabled() {
            return true;
        }
    }

    public static class TermSV extends SchemaVariableModifierSet {
        protected boolean rigidEnabled() {
            return true;
        }

        protected boolean strictEnabled() {
            return true;
        }

        protected boolean listEnabled() {
            return true;
        }
    }

    public static class FormulaSV extends SchemaVariableModifierSet {
        protected boolean rigidEnabled() {
            return true;
        }
    }

    public static class VariableSV extends SchemaVariableModifierSet {
    }

    public static class SkolemTermSV extends SchemaVariableModifierSet {
    }

    public static class FreshProgVarSV extends SchemaVariableModifierSet {
    }

    public static class TermLabelSV extends SchemaVariableModifierSet {
    }
}
