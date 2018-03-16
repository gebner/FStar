(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Ex12.SHA1
open FStar.All
open FStar.Seq
open FStar.Bytes
open CoreCrypto

type text  = b:bytes{UInt.fits (length b) 31}    (* a type abbreviation, for clarity *)


(* we rely on some external crypto library implementing HMAC-SHA1 *)

let keysize = 16ul
let blocksize = keysize
let macsize = 20ul

type key = lbytes32 keysize
type tag = lbytes32 macsize

val sample: n:UInt32.t -> ML (lbytes32 n)
let sample n = random32 n 

val sha1 : bytes -> Tot (h:bytes{length h = 20})
let sha1 b = hash SHA1 b

val hmac_sha1: key -> text -> Tot tag
let hmac_sha1 k t =
  let x5c = byte_of_int 92 in
  let x36 = byte_of_int 54 in
  let opad = create blocksize x5c in
  let ipad = create blocksize x36 in
  let xor_key_opad = xor keysize k opad in
  let xor_key_ipad = xor keysize k ipad in
  sha1 ( xor_key_opad @|
                (sha1 (xor_key_ipad @| t))
       )
