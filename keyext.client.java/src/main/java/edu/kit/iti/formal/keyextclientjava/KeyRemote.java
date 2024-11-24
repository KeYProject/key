package edu.kit.iti.formal.keyextclientjava;

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
        return layer.callSync("meta/version").getAsString();
    }
}