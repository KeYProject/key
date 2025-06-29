/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.keyext.client;

import java.io.IOException;

import edu.kit.iti.formal.keyextclientjava.rpc.KeyRemote;
import edu.kit.iti.formal.keyextclientjava.rpc.RPCLayer;
import org.junit.jupiter.api.Test;

/**
 * @author Alexander Weigl
 * @version 1 (24.11.24)
 */
public class Starter {
    @Test
    void test() throws IOException {
        var file = "../keyext.api/build/libs/keyext.api-2.12.4-dev-all.jar";
        final var rpcLayer = RPCLayer.startWithCLI(file);
        rpcLayer.start();
        var remote = new KeyRemote(rpcLayer);
        System.out.println(remote.meta_version());
    }
}
