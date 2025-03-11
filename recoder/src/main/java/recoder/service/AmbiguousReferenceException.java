/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

import java.util.ArrayList;
import java.util.List;

import recoder.ModelException;
import recoder.abstraction.ProgramModelElement;
import recoder.java.Reference;

/**
 * Exception indicating that a particular reference is ambiguous.
 *
 * @author AL
 */
public class AmbiguousReferenceException extends ModelException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 1106306098306634107L;

    private final Reference reference;

    private final List<? extends ProgramModelElement> choices;

    /**
     * Constructor without explanation text.
     *
     * @param r the ambiguous reference.
     * @param choices the possible resolutions.
     */
    public AmbiguousReferenceException(Reference r, List<? extends ProgramModelElement> choices) {
        reference = r;
        this.choices = choices;
    }

    /**
     * Constructor without explanation text.
     *
     * @param r the ambiguous reference.
     * @param choice1 one possible resolution.
     * @param choice2 a second possible resolution.
     */
    public AmbiguousReferenceException(Reference r, ProgramModelElement choice1,
            ProgramModelElement choice2) {
        reference = r;
        List<ProgramModelElement> list = new ArrayList<>(2);
        list.add(choice1);
        list.add(choice2);
        this.choices = list;
    }

    /**
     * Constructor with an explanation text.
     *
     * @param s an explanation.
     * @param r the ambiguous reference.
     * @param choices the possible resolutions.
     */
    public AmbiguousReferenceException(String s, Reference r,
            List<? extends ProgramModelElement> choices) {
        super(s);
        reference = r;
        this.choices = choices;
    }

    /**
     * Constructor with an explanation text.
     *
     * @param s an explanation.
     * @param r the ambiguous reference.
     * @param choice1 one possible resolution.
     * @param choice2 a second possible resolution.
     */
    public AmbiguousReferenceException(String s, Reference r, ProgramModelElement choice1,
            ProgramModelElement choice2) {
        super(s);
        reference = r;
        List<ProgramModelElement> list = new ArrayList<>(2);
        list.add(choice1);
        list.add(choice2);
        this.choices = list;
    }

    /**
     * Returns the reference that was found ambiguous.
     */
    public Reference getAmbiguousReference() {
        return reference;
    }

    /**
     * Returns the possible choices for the ambiguous reference.
     */
    public List<? extends ProgramModelElement> getPossibleResolutions() {
        return choices;
    }

}
