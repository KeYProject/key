/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.keyextclientjava.rpc;


/**
 * @author Alexander Weigl
 * @version 1 (22.11.24)
 */
public class KeyRemote {
    private final RPCLayer layer;

    public KeyRemote(RPCLayer rpcLayer) {
        this.layer = rpcLayer;
    }

    public String meta_version() {
        final var obj = layer.callSync("meta/version");
        return obj.get("result").getAsString();
    }
}
