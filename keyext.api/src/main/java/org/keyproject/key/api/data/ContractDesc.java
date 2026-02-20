/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.speclang.Contract;

/**
 * Description of a loadable contract in KeY.
 *
 * Contracts can be arbitrary objects, representing a functional, dependency, information flow, etc.
 * contract.
 * Contracts can be loaded into proofs.
 *
 * @param contractId an identifier of the contract
 * @param name Name of the contract
 * @param displayName Showable name
 * @param typeName the typename which is associated with this contract
 * @param htmlText content of the contract as html text
 * @param plainText content of the contract as plain text
 *
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
public record ContractDesc(KeyIdentifications.ContractId contractId, String name,
        String displayName, String typeName, String htmlText, String plainText)
        implements KeYDataTransferObject {
    public static ContractDesc from(KeyIdentifications.EnvironmentId envId,
            Services services, Contract it) {
        return new ContractDesc(new KeyIdentifications.ContractId(envId, it.getName()),
            it.getName(), it.getDisplayName(), it.getTypeName(),
            it.getHTMLText(services), it.getPlainText(services));
    }
}
