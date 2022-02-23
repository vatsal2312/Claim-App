// SPDX-License-Identifier: MIT

import "./console.sol";

pragma solidity ^0.8.0;

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(
        address indexed previousOwner,
        address indexed newOwner
    );

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _transferOwnership(_msgSender());
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(
            newOwner != address(0),
            "Ownable: new owner is the zero address"
        );
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

pragma solidity ^0.8.0;

interface IToken {
    function transferFrom(
        address from,
        address to,
        uint256 value
    ) external returns (bool);

    function transfer(address to, uint256 value) external returns (bool);

    function decimals() external returns (uint256);

    function balanceOf(address who) external view returns (uint256);

    function mintedSupply() external returns (uint256);

    function allowance(address owner, address spender)
        external
        view
        returns (uint256);

    function approve(address spender, uint256 value) external returns (bool);
}

contract Airdrop is Ownable {
    address public flushAddress;
    mapping(bytes32 => Root) public merkleRoots;
    mapping(address => bytes32) public tokenMerkleRoot;
    mapping(bytes32 => mapping(address => bool)) public userClaims;
    bool _reentrancyLock = false;
    mapping(bytes32 => uint256) public totalClaimed;
    mapping(string => bool) public names;

    struct Root {
        uint256 deadline;
        bytes32 root;
        string name;
    }

    modifier noReentrancy() {
        require(!_reentrancyLock, "Is processing");
        _reentrancyLock = true;
        _;
        _reentrancyLock = false;
    }

    event AirdropClaimed(
        bytes airdrop,
        address indexed addr,
        uint256 amount,
        bytes32 root
    );

    constructor(address flushAddress_, Root[] memory roots) {
        flushAddress = flushAddress_;
        for (uint256 i = 0; i < roots.length; i++) {
            merkleRoots[roots[i].root] = Root({
                deadline: roots[i].deadline,
                root: roots[i].root,
                name: roots[i].name
            });
            names[roots[i].name] = true;
        }
    }

    function addAirdrop(Root memory root_) public onlyOwner {
        require(!names[root_.name], "Airdrop name must be unique");
        merkleRoots[root_.root] = root_;
    }

    function setFlushAddress(address flushAddress_) public onlyOwner {
        require(flushAddress_ != address(0), "Cannot be address(0)");
        flushAddress = flushAddress_;
    }

    function setDeadline(bytes32 root_, uint256 deadline_) public onlyOwner {
        require(merkleRoots[root_].root == root_, "Airdrop root not found");
        merkleRoots[root_].deadline = deadline_;
    }

    /**
     * @dev Claim airdrops
     * @param name title of airdrop program
     * @param token token to be claimed
     * @param amount amount to be claimed
     * @param merkleRoot merkle root of airdrop
     * @param merkleProof merkle proof for user
     */
    function claim(
        string memory name,
        address token,
        uint256 amount,
        bytes32 merkleRoot,
        bytes32[] calldata merkleProof
    ) public noReentrancy {
        address account = msg.sender;
        require(
            canClaim(account, name, token, amount, merkleRoot, merkleProof),
            "Unable to claim"
        );
        userClaims[merkleRoot][account] = true;
        totalClaimed[merkleRoot] += amount;
        IToken(token).transfer(account, amount);
        emit AirdropClaimed(bytes(name), account, amount, merkleRoot);
    }

    /**
     * @dev check if user with `account` can claim `amount` of `token` from airdrop `name`
     * @param name title of airdrop program
     * @param token token to be claimed
     * @param amount amount to be claimed
     * @param merkleRoot merkle root of airdrop
     * @param merkleProof merkle proof for user
     * @return bool if user can claim
     */
    function canClaim(
        address account,
        string memory name,
        address token,
        uint256 amount,
        bytes32 merkleRoot,
        bytes32[] calldata merkleProof
    ) public view returns (bool) {
        require(
            merkleRoots[merkleRoot].deadline > block.timestamp,
            "Invalid airdrop"
        );
        require(
            keccak256(bytes(merkleRoots[merkleRoot].name)) ==
                keccak256(bytes(name)),
            "Invalid name"
        );
        require(!userClaims[merkleRoot][account], "Already claimed");
        bytes32 node = keccak256(
            abi.encodePacked(token, bytes(name), account, amount)
        );
        // console.log("element %s", node);
        // Verify the merkle proof.
        require(
            MerkleProof.verify(merkleProof, merkleRoot, node),
            "Airdrop: Invalid proof."
        );

        return true;
    }

    function flush(address token_) public onlyOwner {
        IToken token = IToken(token_);
        token.transfer(flushAddress, token.balanceOf(address(this)));
    }
}

// OpenZeppelin Contracts v4.4.1 (utils/cryptography/MerkleProof.sol)

pragma solidity ^0.8.0;

/**
 * @dev These functions deal with verification of Merkle Trees proofs.
 *
 * The proofs can be generated using the JavaScript library
 * https://github.com/miguelmota/merkletreejs[merkletreejs].
 * Note: the hashing algorithm should be keccak256 and pair sorting should be enabled.
 *
 * See `test/utils/cryptography/MerkleProof.test.js` for some examples.
 */
library MerkleProof {
    /**
     * @dev Returns true if a `leaf` can be proved to be a part of a Merkle tree
     * defined by `root`. For this, a `proof` must be provided, containing
     * sibling hashes on the branch from the leaf to the root of the tree. Each
     * pair of leaves and each pair of pre-images are assumed to be sorted.
     */
    function verify(
        bytes32[] memory proof,
        bytes32 root,
        bytes32 leaf
    ) internal pure returns (bool) {
        return processProof(proof, leaf) == root;
    }

    /**
     * @dev Returns the rebuilt hash obtained by traversing a Merklee tree up
     * from `leaf` using `proof`. A `proof` is valid if and only if the rebuilt
     * hash matches the root of the tree. When processing the proof, the pairs
     * of leafs & pre-images are assumed to be sorted.
     *
     * _Available since v4.4._
     */
    function processProof(bytes32[] memory proof, bytes32 leaf)
        internal
        pure
        returns (bytes32)
    {
        bytes32 computedHash = leaf;
        for (uint256 i = 0; i < proof.length; i++) {
            bytes32 proofElement = proof[i];
            if (computedHash <= proofElement) {
                // Hash(current computed hash + current element of the proof)
                computedHash = keccak256(
                    abi.encodePacked(computedHash, proofElement)
                );
            } else {
                // Hash(current element of the proof + current computed hash)
                computedHash = keccak256(
                    abi.encodePacked(proofElement, computedHash)
                );
            }
        }
        return computedHash;
    }
}
