package de.uka.ilkd.key.gui.isabelletranslation;

import scala.Tuple2;
import scala.collection.immutable.List;

public record SledgehammerResult(Tuple2<Object, Tuple2<String, List<String>>> result) {
    public Boolean isSuccessful() {
        return (Boolean) result._1();
    }

    public String getSuccessfulTactic() {
        if (!isSuccessful()) {
            return null;
        }
        return result._2()._2().head();
    }

    @Override
    public String toString() {
        return result.toString();
    }
}
