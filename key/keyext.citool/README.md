
#KeY: ci-tool 1.1.0

ci-tool is a utility for supporting Java and JML contracts in Continuous Integration pipelines 
by providing support for checking the proofability of JML with [KeY](https://key-project.org).

ci-tool is licensed under GPLv2+.

If you any suggestion feel to contact: [Alexander Weigl](https://formal.iti.kit.edu/weigl).

## Usage:

To use the ci-tool add the following lines to the ci config.

1. Get the latest version from the server:
```bash
$ wget -O ci-tool.jar  https://key-project.org/ci-tool
```

2. Call ci-tool with your key-files or java file (or folder).
   ci-tool tries to verify all proofs automatically and uses found proofs or script files.
   
```bash 
$ java -jar <jarfile> [files]
```

3. Find more parameters with `-h`

```bash 
$ java -jar <jarfile> -h 
```


### Examples

For travis-ci:

```yaml
jdk:
  - openjdk11

language: java
install:
  - wget -O ci-tool.jar  https://key-project.org/ci-tool
script:
  - javac simplified/Keyserver.java
  - java -jar ci-tool.jar simplified/Keyserver.java
```

## Changelog

* [1.1.0](https://formal.iti.kit.edu/ci-tool/keyext.citool-1.1.0-all.jar): bug fixes and support for proofs in key-files
  - Change of console output 
  - Fix loading of proof files
  - Add download URL and a website
  - Known Bug: Something with the proof (search) path is wrong.

* [1.0.0](https://formal.iti.kit.edu/ci-tool/keyext.citool-1.0.0-all.jar) initial working version (*24.01.2020*)
  - first release of this project after positive of the a small `jshell` utility.
  - deploy on VerifyThis LTC 2020 repository  
  
  
## Future features

* Accumulate statistics
* If proof remains open, 
* Calculate a coverage based on statements in the 
