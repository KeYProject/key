package org.key_project.isabelletranslation;

import scala.Option;
import scala.Tuple2;

public record SledgehammerResult(Option<Tuple2<String, String>> result) {
    public Boolean isSuccessful() {
        return result.exists((Tuple2<String, String> tactic) -> !tactic._1().equals("timeout"));
    }

    public String getSuccessfulTactic() {
        if (!isSuccessful()) {
            return null;
        }
        return result.get()._2();
    }

    @Override
    public String toString() {
        return (result.exists((r) -> true)) ? result.get().toString() : null;
    }

    public boolean isTimeout() {
        return result.exists((Tuple2<String, String> tactic) -> tactic._1().equals("timeout"));
    }
}
