/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.proof.mgt;

import java.util.EventListener;

public interface ProofEnvironmentListener extends EventListener {

    public void proofRegistered(ProofEnvironmentEvent event);

    public void proofUnregistered(ProofEnvironmentEvent event);


}
