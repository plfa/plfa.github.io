#!/usr/bin/env bash

# Sends out marks for students based on the folder structure used by Submit,
# the coursework submission system used in the School of Informatics at the
# University of Edinburgh.
#
# This script assumes the following folder structure:
#
#   $DIR/sXXXXXXX/cw$CW/$FILE
#
# The variable DIR refers to the directory passed in as an argument to the
# script. The variable XXXXXXX refers to the student ID, and it is assumed
# that
#
#   sXXXXXXX@sms.ed.ac.uk
#
# is a valid email address. The variable $CW refers to the number for of the
# coursework of which the students are meant to be notified. The directory
# DIR/sXXXXXXX/cwY/ should only contain a single file, which should be
# specified using the FILE parameter.
#
# Usage:
#
#   ./send_marks.sh [DIR] [CW] [FILE]

DIR="$1"
shift

CW="$1"
shift

FILE="$1"
shift

for ATTACHMENT in "${DIR%/}/s"*"/cw$CW/$FILE"; do
    SUBJ="Mark for coursework $CW"
    BODY=""
    SID=$(echo "$ATTACHMENT" | sed 's|.*/\(s[0-9]\{7\}\)/.*|\1|')
    ADDR="$SID@sms.ed.ac.uk"
    CMD="echo \"$BODY\" | mail -s \"$SUBJ\" -a \"$ATTACHMENT\" \"$ADDR\""
    echo "You are about to run the following command:"
    echo -e "\n$CMD\n"
    read -p "Are you sure? " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]
    then
        eval "$CMD"
    fi
done
