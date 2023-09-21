/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
