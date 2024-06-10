module Pact.Core.Command.Client where

import Pact.Core.Command.Types
import Pact.Core.Command.Crypto

-- CREATING AND SIGNING TRANSACTIONS

mkCommand
  :: J.Encode c
  => J.Encode m
  => [(Ed25519KeyPair, [SigCapability])]
  -> [Verifier ParsedVerifierProof]
  -> m
  -> Text
  -> Maybe NetworkId
  -> PactRPC c
  -> IO (Command ByteString)
mkCommand creds vers meta nonce nid rpc = mkCommand' creds encodedPayload
  where
    encodedPayload = J.encodeStrict $ toLegacyJsonViaEncode payload
    payload = Payload rpc nonce meta (keyPairsToSigners creds) (vers <$ guard (not (null vers))) nid

data WebAuthnPubKeyPrefixed
  = WebAuthnPubKeyPrefixed
  | WebAuthnPubKeyBare
  deriving (Eq, Show, Generic)
data DynKeyPair
  = DynEd25519KeyPair Ed25519KeyPair
  | DynWebAuthnKeyPair WebAuthnPubKeyPrefixed WebAuthnPublicKey WebauthnPrivateKey
  deriving (Eq, Show, Generic)


keyPairToSigner :: Ed25519KeyPair -> [UserCapability] -> Signer
keyPairToSigner cred caps = Signer scheme pub addr caps
      where
        scheme = Nothing
        pub = toB16Text $ exportEd25519PubKey $ fst cred
        addr = Nothing

keyPairsToSigners :: [Ed25519KeyPairCaps] -> [Signer]
keyPairsToSigners creds = map (uncurry keyPairToSigner) creds

signHash :: TypedHash h -> Ed25519KeyPair -> Text
signHash hsh (pub,priv) =
  toB16Text $ exportEd25519Signature $ signEd25519 pub priv (toUntypedHash hsh)

mkUnsignedCommand
  :: J.Encode m
  => J.Encode c
  => [Signer]
  -> [Verifier ParsedVerifierProof]
  -> m
  -> Text
  -> Maybe NetworkId
  -> PactRPC c
  -> IO (Command ByteString)
mkUnsignedCommand signers vers meta nonce nid rpc = mkCommand' [] encodedPayload
  where encodedPayload = J.encodeStrict payload
        payload = Payload rpc nonce meta signers (vers <$ guard (not (null vers))) nid


mkCommand' :: [(Ed25519KeyPair ,a)] -> ByteString -> IO (Command ByteString)
mkCommand' creds env = do
  let hsh = hash env    -- hash associated with a Command, aka a Command's Request Key
      toUserSig (cred,_) = ED25519Sig $ signHash hsh cred
  let sigs = toUserSig <$> creds
  return $ Command env sigs hsh


-- | A utility function used for testing.
-- It generalizes `mkCommand` by taking a `DynKeyPair`, which could contain mock
-- WebAuthn keys. If WebAuthn keys are encountered, this function does mock WebAuthn
-- signature generation when constructing the `Command`.
mkCommandWithDynKeys' :: [(DynKeyPair, a)] -> ByteString -> IO (Command ByteString)
mkCommandWithDynKeys' creds env = do
  let hsh = hash env    -- hash associated with a Command, aka a Command's Request Key
  sigs <- traverse (toUserSig hsh) creds
  return $ Command env sigs hsh
  where
    toUserSig :: PactHash.Hash -> (DynKeyPair, a) -> IO UserSig
    toUserSig hsh = \case
      (DynEd25519KeyPair (pub, priv), _) ->
        pure $ ED25519Sig $ signHash hsh (pub, priv)
      (DynWebAuthnKeyPair _ pubWebAuthn privWebAuthn, _) -> do
        signResult <- runExceptT $ signWebauthn pubWebAuthn privWebAuthn "" (toUntypedHash hsh)
        case signResult of
          Left e -> error $ "Failed to sign with mock WebAuthn keypair: " ++ e
          Right sig -> return $ WebAuthnSig sig



mkCommandWithDynKeys
  :: J.Encode c
  => J.Encode m
  => [(DynKeyPair, [UserCapability])]
  -> [Verifier ParsedVerifierProof]
  -> m
  -> Text
  -> Maybe NetworkId
  -> PactRPC c
  -> IO (Command ByteString)
mkCommandWithDynKeys creds vers meta nonce nid rpc = mkCommandWithDynKeys' creds encodedPayload
  where
    encodedPayload = J.encodeStrict $ toLegacyJsonViaEncode payload
    payload = Payload rpc nonce meta (map credToSigner creds) (vers <$ guard (not (null vers))) nid
    credToSigner cred =
      case cred of
        (DynEd25519KeyPair (pubEd25519, _), caps) ->
          Signer
            { _siScheme = Nothing
            , _siPubKey = toB16Text (exportEd25519PubKey pubEd25519)
            , _siAddress = Nothing
            , _siCapList = caps
            }
        (DynWebAuthnKeyPair isPrefixed pubWebAuthn _, caps) ->
          let
            prefix = case isPrefixed of
              WebAuthnPubKeyBare -> ""
              WebAuthnPubKeyPrefixed -> webAuthnPrefix
          in Signer
            { _siScheme = Just WebAuthn
            , _siPubKey = prefix <> toB16Text (exportWebAuthnPublicKey pubWebAuthn)
            , _siAddress = Nothing
            , _siCapList = caps
            }