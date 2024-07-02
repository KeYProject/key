// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.recoderext;

import recoder.java.SourceVisitor;

/**
 * Adds visitor methods for recoder extensions.
 *
 * @author bubel
 *
 */
public class SourceVisitorExtended extends SourceVisitor {

    public void visitCatchAll(CatchAllStatement x) {
        // default do nothing
    }

    public void visitExec(Exec exec) {
        // default do nothing
    }

    public void visitCcatch(Ccatch ccatch) {
        // default do nothing
    }

    public void visitCcatchReturnParameterDeclaration(
            CcatchReturnParameterDeclaration ccatchReturnParameterDeclaration) {
        // default do nothing
    }

    public void visitCcatchReturnValParameterDeclaration(
            CcatchReturnValParameterDeclaration ccatchReturnValParameterDeclaration) {
        // default do nothing
    }

    public void visitCcatchBreakParameterDeclaration(
            CcatchBreakParameterDeclaration ccatchBreakParameterDeclaration) {
        // default do nothing
    }

    public void visitCcatchContinueParameterDeclaration(
            CcatchContinueParameterDeclaration ccatchContinueParameterDeclaration) {
        // default do nothing
    }

    public void visitCcatchBreakLabelParameterDeclaration(
            CcatchBreakLabelParameterDeclaration ccatchBreakLabelParameterDeclaration) {
        // default do nothing
    }

    public void visitCcatchContinueLabelParameterDeclaration(
            CcatchContinueLabelParameterDeclaration ccatchContinueLabelParameterDeclaration) {
        // default do nothing
    }

    public void visitCcatchContinueWildcardParameterDeclaration(
            CcatchContinueWildcardParameterDeclaration ccatchContinueWildcardParameterDeclaration) {
        // default do nothing
    }

    public void visitCcatchReturnWildcardParameterDeclaration(
            CcatchBreakWildcardParameterDeclaration ccatchReturnWildcardParameterDeclaration) {
        // default do nothing
    }

}