#!/bin/bash

# Dependencies:
# - curl <https://curl.haxx.se/>
# - yq <https://github.com/mikefarah/yq>

# Modify .travis.yml:
# - Remove 'script' and 'deploy' phases;
# - Add 'merge_mode';
# - Create JSON request.
#
body=$(cat .travis.yml \
                       | yq w - script "echo 'Done'"\
                       | yq d - before_deploy \
                       | yq d - deploy \
                       | yq p - config \
                       | yq w - message "Build cache" \
                       | yq w - branch dev \
                       | yq w - merge_mode replace \
                       | yq p - request -j)

# Send request to Travis.
#
resp=$(curl -s -X POST \
                  -H "Content-Type: application/json" \
                  -H "Accept: application/json" \
                  -H "Travis-API-Version: 3" \
                  -H "Authorization: token $TRAVIS_TOKEN" \
                  -d "$body" \
                  https://api.travis-ci.org/repo/plfa%2Fplfa.github.io/requests)

# Output response.
#
echo "$resp" \
    | yq d - request.configs \
    | yq d - request.config \
    | yq r - --prettyPrint

# Output configuration.
#
echo "$resp" \
    | yq r - request.config \
    | yq p - config \
    | yq r - --prettyPrint
