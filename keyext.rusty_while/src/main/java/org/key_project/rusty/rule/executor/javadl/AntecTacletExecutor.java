/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.executor.javadl;

import org.key_project.rusty.rule.AntecTaclet;

/**
 * Executes a Taclet which matches on a formula in the antecedent
 *
 * @author Richard Bubel
 * @param <TacletKind> the kind of taclet this executor is responsible for
 */
public class AntecTacletExecutor<TacletKind extends AntecTaclet>
        extends FindTacletExecutor<TacletKind> {

    public AntecTacletExecutor(TacletKind taclet) {
        super(taclet);
    }
}
