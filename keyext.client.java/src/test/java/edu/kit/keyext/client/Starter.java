package edu.kit.keyext.client;

import edu.kit.iti.formal.keyextclientjava.rpc.KeyRemote;
import edu.kit.iti.formal.keyextclientjava.rpc.RPCLayer;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * @author Alexander Weigl
 * @version 1 (24.11.24)
 */
public class Starter {
    @Test
    void test() throws IOException {
        var file = "/home/weigl/work/key/keyext.api/build/libs/keyext.api-2.12.4-dev-all.jar";
        final var rpcLayer = RPCLayer.startWithCLI(file);
        rpcLayer.start();
        var remote = new KeyRemote(rpcLayer);
        System.out.println(remote.meta_version());
    }
}
