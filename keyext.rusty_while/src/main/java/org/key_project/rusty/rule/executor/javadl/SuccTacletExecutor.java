/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.executor.javadl;

import org.key_project.rusty.rule.SuccTaclet;

public class SuccTacletExecutor<TacletKind extends SuccTaclet>
        extends FindTacletExecutor<TacletKind> {

    public SuccTacletExecutor(TacletKind taclet) {
        super(taclet);
    }
}
