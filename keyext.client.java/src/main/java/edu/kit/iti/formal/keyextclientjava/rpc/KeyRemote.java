package edu.kit.iti.formal.keyextclientjava.rpc;

import com.google.gson.JsonObject;

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