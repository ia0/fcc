#!/bin/zsh

echo 'Require Import Llanguage.'
echo 'Require Import typesystem.'
echo 'Require Import Ltypesystem.'
echo 'Require Import typechecker.'
echo ''
echo 'Eval compute in (atcj true HNil GNil ('
../../src/l2c.native || exit 1
echo ')).'
