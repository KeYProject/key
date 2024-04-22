package org.key_project;

import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.smt.lang.Util;
import io.reactivex.internal.queue.SpscArrayQueue;
import org.key_project.prompts.Gpt3Prompt;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class Benchmark {
    public static String[] benchmarks = {
//        "2-Pot-contract.java",
//        "3-setSize-contract.java",
//        "4-getSize-contract.java",
//        "5-addToPotSize-contract.java",
//        "6-Card-contract.java",
//        "7-setRank-contract.java",
//        "8-setSuit-contract.java",
//        "9-getRank-contract.java",
//        "10-getSuit-contract.java",
//        "11-Arc-contract.java",
//        "12-flip-contract.java",
//        "13-equals-contract.java",
//        "14-className-contract.java",
//        "15-setTarget-contract.java",
//        "16-getTarget-contract.java",
//        "17-initilize-contract.java",
//        "18-getAllCards-contract.java",
//        "19-setAllCards-contract.java",
//        "20-addToBank-subcontract-setBank.java",
//        "21-subtractFromBank-subcontract-setBank.java",
//        "22-setBank-contract.java",
//        "23-parseNonce-contract.java",
//        "24-parseContentLength-contract.java",
//        "25-deserialize-contract.java",
//        "26-getNonce-contract.java",
//        "27-getLong-contract.java",
//        "28-getInt-contract.java",
//        "29-parseLong-contract.java",
//        "30-parseInt-contract.java",
//        "31-getShort-contract.java",
//        "32-parseShort-contract.java",
//        "33-Loop1-contract.java",
//        "34-method1-invariant.java",
//        "36-method1-contract.java",
//        "37-gcd-subcontract-gcdHelp.java",
////        "38-gcdHelp-invariant.java",
//        "39-addAbsoluteValues-contract.java",
//        "40-square-invariant.java",
//        "41-add-contract.java",
//        "42-addWithJump-contract.java",
//        "43-addWithTwoBlockContracts-contract.java",
//      "46-unnecessaryLoopInvariant-invariant.java",
//        "47-generateByteArray-contract.java",
//        "48-getLength-contract.java",
//        "49-swap-contract.java",
//        "50-twoWaySort-subcontract-swap.java",
//        "51-sum3-invariant.java",
//        "52-sum2-invariant.java",
//        "53-sum1-invariant.java",
//        "54-sum0-invariant.java",
//        "55-coincidenceCount1-invariant.java",
//        "56-isPow2-contract.java",
//        "57-pow2-contract.java",
//        "58-div2-contract.java",
//        "59-even-contract.java",
//       "61-min-invariant.java",
//        "62-f-contract.java",
//        "65-downsweep-subcontract-even,bin2,div2,isPow2.java",
//        "65@1-downsweep-subcontract-even.java",
//        "65@2-downsweep-subcontract-pow2.java",
//        "65@3-downsweep-subcontract-div2.java",
//        "65@4-downsweep-subcontract-isPow2.java",
//        "66-main-subcontract-downsweep.java",
//        "67-test-contract.java",
//        "68-m-contract.java",
//        "69-gcd-contract.java",
//        "71-daysInMoth-contract.ava",
//        "76-twoWaySort-invariant.java",
//        "78-isValid-contract.java",
//        "79-charge-contract.java",
//        "80-computeHealthState-invariant.java",
//        "81-coincidenceCount1-contract.java",
//        "82-sum0-contract.java",
//        "83-sum1-contract.java",
//        "84-sum2-contract.java",
//        "85-sum3-contract.java",
//        "86-mult-invariant.java",
//        "87-cubicSum-invariant.java",
//        "88-f-contract.java",
        "90-reverse2-invariant.java",
        "91-reverse-invariant.java",
        "92-max-invariant.java",
        "93-average-invariant.java",
//        "95-assignA-contract.java",
//        "96-assignB-contract.java",
//        "97-IsSymmetric-contract.java",
//        "98-simpleSanitize-contract.java",
//        "99-contains-contract.java",
//        "100-insert-contract.java",
        "101-m-invariant.java",
        "102-sort-invariant.java",
//        "103-max-contract.java",
//        "104-average-contract.java",
//        "107-reverse-contract.java",
//        "108-reverse2-contract.java",
//        "109-m-contract.java"
    };
    private static String resFile = "/home/pat/uni/prak-gpt/data/bench_results.csv";
    private static String errFile = "/home/pat/uni/prak-gpt/data/bench_errors.txt";
    private static int maxlen = -1;
    public static int maxBMLen() {
        if (maxlen == -1) {
            maxlen = Arrays.stream(benchmarks).mapToInt(String::length).max().orElse(0);
        }
        return maxlen;
    }
    private static String padded(String topad) {
        return String.format("%"+maxBMLen()+"s",topad);
    }

    String name;
    int[] result;
    private String repr = null;

    public Benchmark(String n, boolean[] r) {
        name = n;
        result = new int[r.length];
        for(int i = 0; i < r.length; i++)
            result[i] = r[i] ? 1 : 0;
    }

    public String getRepr() {
        if (repr == null) {
            repr = padded(name);
            repr += Arrays.stream(result).mapToObj(b -> b > 0 ? ",1" : ",0").collect(Collectors.joining(""));
        }
        return repr;
    }

    public static Benchmark onClass(String classDir, String _class, String token, int maxTries, Path tmpFile, int repeats) throws Exception {
        String[] vs;
        {
            String s = _class;
            s = s.substring(0, s.lastIndexOf(".java"));
            vs = s.split("-");
        }
        String id = vs[0];
        String topmthd = vs[1];
        String task = vs[2];
        Path location = Path.of(classDir, _class);
        List<String> classLines = Files.readAllLines(location);
        String name = _class;
        boolean isCtor = _class.equals(topmthd);
        boolean[] res = new boolean[repeats];
        switch (task) {
            case "contract":
                for (int i = 0; i < repeats; i++) {
                    try {
                        boolean succ = Gpt3Prompt.specifyFunction(token, classLines, topmthd, isCtor, null, false, maxTries, tmpFile);
                        res[i] = succ;
                    } catch  (TermCreationException e) {
                        Utility.appendToFile(errFile, "TermCreation failed in " + _class);
                        Utility.appendToFile(errFile, e.toString() + "\n");
                        return null;
                    } catch (Exception e) {
                        res[i] = false;
                        continue;
                    }
                }
            case "subcontract":
                String subfunc = vs[3];
                for (int i = 0; i < repeats; i++) {
                    try {
                        boolean succ = Gpt3Prompt.specifyFunction(token, classLines, topmthd, isCtor, subfunc, false, maxTries, tmpFile);
                        res[i] = succ;
                    } catch  (TermCreationException e) {
                        Utility.appendToFile(errFile, "TermCreation failed in " + _class);
                        Utility.appendToFile(errFile, e.toString() + "\n");
                        return null;
                    } catch (Exception e) {
                        res[i] = false;
                        continue;
                    }
                }
            case "invariant":
                for (int i = 0; i < repeats; i++) {
                    try {
                        boolean succ = Gpt3Prompt.specifyFunction(token, classLines, topmthd, isCtor, null, true, maxTries, tmpFile);
                        res[i] = succ;
                    } catch  (TermCreationException e) {
                        Utility.appendToFile(errFile, "TermCreation failed in " + _class);
                        Utility.appendToFile(errFile, e.toString() + "\n");
                        return null;
                    } catch (Exception e) {
                        res[i] = false;
                        continue;
                    }
                }
            default:
        }
        var b = new Benchmark(name, res);
        Utility.appendToFile(resFile, b.getRepr());
        return b;
    }
}
