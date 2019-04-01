pipeline {
  agent any

  environment {
      GRADLE_OPTS = '-Dorg.gradle.daemon=false'
  }

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
            junit(testResults: '*/*/build/test-results/test/*.xml', allowEmptyResults: true, healthScaleFactor: 1)

          }
        }
        stage('key.ui') {
          steps {
            sh '''cd key
./gradlew --build-cache --continue :key.ui:check
'''
            junit(testResults: '*/*/build/test-results/test/*.xml', allowEmptyResults: true, healthScaleFactor: 1)
          }
        }
        stage('Test: proof_references') {
          steps {
            sh '''cd key
./gradlew --build-cache --continue :key.core.proof_references:check
'''
            junit(testResults: '*/*/build/test-results/test/*.xml', allowEmptyResults: true, healthScaleFactor: 1)

          }
        }
        stage('Test: key.removegenerics') {
          steps {
            sh '''cd key
./gradlew --build-cache --continue :key.removegenerics:check
'''
            junit(testResults: '*/*/build/test-results/test/*.xml', allowEmptyResults: true, healthScaleFactor: 1)
          }
        }
        stage('Test: key.core.testgen') {
          steps {
            sh '''cd key
./gradlew --build-cache --continue :key.core.testgen:check
'''
            junit(testResults: '*/*/build/test-results/test/*.xml', allowEmptyResults: true, healthScaleFactor: 1)
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
            junit(testResults: '*/*/build/test-results/test/*.xml', allowEmptyResults: true, healthScaleFactor: 1)
          }
        }
        stage('Test: ProofRules') {
          steps {
            sh '''cd key
./gradlew --build-cache --continue :key.core:testProofRules
'''
            junit(testResults: '*/*/build/test-results/test/*.xml', allowEmptyResults: true, healthScaleFactor: 1)
          }
        }
      }
    }
  }
}