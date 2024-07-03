/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ldt;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.rusty.Services;

public class BoolLDT extends LDT {
    public static final Name NAME = new Name("bool");

    /** the boolean literals as function symbols and terms */
    private final Function bool_true;
    private final Term term_bool_true;
    private final Function bool_false;
    private final Term term_bool_false;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public BoolLDT(Services services) {
        super(NAME, services);

        bool_true = addFunction(services, "TRUE");
        term_bool_true = services.getTermBuilder().func(bool_true);
        bool_false = addFunction(services, "FALSE");
        term_bool_false = services.getTermBuilder().func(bool_false);
    }


    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    public Term getFalseTerm() {
        return term_bool_false;
    }


    public Term getTrueTerm() {
        return term_bool_true;
    }


    /**
     * returns the function representing the boolean value <tt>FALSE</tt>
     */
    public Function getFalseConst() {
        return bool_false;
    }


    /**
     * returns the function representing the boolean value <tt>TRUE</tt>
     */
    public Function getTrueConst() {
        return bool_true;
    }


    @Override
    public Name name() {
        return NAME;
    }
}
