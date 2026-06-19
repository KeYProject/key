/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.proof.mgt.SpecificationRepository;

/**
 *
 * @author Alexander Weigl
 * @version 1 (1/1/26)
 */
public interface TacletPOGenerator {
    void generate(AbstractPO abstractPO, InitConfig initConfig, SpecificationRepository specRepo);
}
