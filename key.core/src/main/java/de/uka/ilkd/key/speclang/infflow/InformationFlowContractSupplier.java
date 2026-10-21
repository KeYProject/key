/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.infflow;

/**
 * @author Alexander Weigl
 * @version 1 (8/3/25)
 */
public interface InformationFlowContractSupplier {
    InformationFlowContract create(InformationFlowContractInfo info);
}
