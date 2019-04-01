pipeline {
  agent any
  stages {
    stage('Compile') {
      steps {
        sh '''cd key
pwd
ls -l'''
        sh 'cd key; ./gradlew classes'
      }
    }
    stage('Compile Tests') {
      steps {
        sh '''javac -version
cd key
./gradlew --build-cache testClasses'''
      }
    }
    stage('Test: key.util') {
      parallel {
        stage('Test: key.util') {
          steps {
            sh '''cd key
./gradlew --build-cache --continue :key.util:check
'''
            junit(testResults: '*/*/build/test-results/test/*.xml', allowEmptyResults: true, healthScaleFactor: 1)
          }
        }
        stage('Test: key.core') {
          steps {
            sh '''cd key
./gradlew --build-cache --continue :key.core:check
'''
          }
        }
        stage('key.ui') {
          steps {
            sh '''cd key
./gradlew --build-cache --continue :key.ui:check
'''
          }
        }
        stage('Test: proof_references') {
          steps {
            sh '''cd key
./gradlew --build-cache --continue :key.core.proof_references:check
'''
          }
        }
        stage('Test: key.removegenerics') {
          steps {
            sh '''cd key
./gradlew --build-cache --continue :key.removegenerics
'''
          }
        }
        stage('Test: key.core.testgen') {
          steps {
            sh '''cd key
./gradlew --build-cache --continue :key.core.testgen:check
'''
          }
        }
      }
    }
    stage('Test: Run All Proofs') {
      parallel {
        stage('Test: Run All Proofs') {
          steps {
            sh '''javac -version
cd key
./gradlew --build-cache --continue :key.core:testRunAllProofs
ls'''
            junit '*/*/build/test-results/test/*.xml'
          }
        }
        stage('Test: ProofRules') {
          steps {
            sh '''cd key
./gradlew --build-cache --continue :key.core:testProofRules

ls -l*/*/build/test-results/test/*.xml'''
            junit '*/*/build/test-results/test/*.xml'
          }
        }
      }
    }
  }
}