#!/bin/sh
export PATH="/usr/lib/jvm/jre-1.6.0/bin/:$PATH"
javac bank/*.java && jpf bank.jpf
