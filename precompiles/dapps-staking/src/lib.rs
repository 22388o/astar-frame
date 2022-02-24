//! Astar dApps staking interface.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode};
use fp_evm::{Context, ExitSucceed, PrecompileFailure, PrecompileOutput};

use frame_support::{
    dispatch::{Dispatchable, GetDispatchInfo, PostDispatchInfo},
    traits::{Currency, Get},
};
use pallet_evm::{AddressMapping, Precompile};
use precompile_utils::{
    Address, EvmData, EvmDataReader, EvmDataWriter, EvmResult, FunctionModifier, Gasometer,
    RuntimeHelper,
};
use sp_core::H160;
use sp_runtime::traits::Zero;
use sp_std::{convert::TryInto, marker::PhantomData, vec::Vec};
extern crate alloc;

type BalanceOf<Runtime> = <<Runtime as pallet_dapps_staking::Config>::Currency as Currency<
    <Runtime as frame_system::Config>::AccountId,
>>::Balance;

mod utils;
pub use utils::*;
#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

pub struct DappsStakingWrapper<R>(PhantomData<R>);

// Runtime: parachain_staking::Config + pallet_evm::Config,

// BalanceOf<Runtime>: EvmData,
// Runtime::Call: Dispatchable<PostInfo = PostDispatchInfo> + GetDispatchInfo,
// <Runtime::Call as Dispatchable>::Origin: From<Option<Runtime::AccountId>>,
// Runtime::Call: From<parachain_staking::Call<Runtime>>,

impl<R> DappsStakingWrapper<R>
where
    R: pallet_evm::Config + pallet_dapps_staking::Config,
    BalanceOf<R>: EvmData,
    <R::Call as Dispatchable>::Origin: From<Option<R::AccountId>>,
    R::Call: From<pallet_dapps_staking::Call<R>>,
{
    /// Fetch current era from CurrentEra storage map
    fn read_current_era(gasometer: &mut Gasometer) -> EvmResult<PrecompileOutput> {
        gasometer.record_cost(RuntimeHelper::<R>::db_read_gas_cost())?;
        let current_era = pallet_dapps_staking::CurrentEra::<R>::get();

        let output = EvmDataWriter::new().write(current_era).build();
        println!("read_current_era output: {:?}", output);

        Ok(PrecompileOutput {
            exit_status: ExitSucceed::Returned,
            cost: gasometer.used_gas(),
            output,
            logs: Default::default(),
        })
    }
    /// Fetch unbonding period
    fn read_unbonding_period(gasometer: &mut Gasometer) -> EvmResult<PrecompileOutput> {
        gasometer.record_cost(RuntimeHelper::<R>::db_read_gas_cost())?;
        let unbonding_period = R::UnbondingPeriod::get();

        let output = EvmDataWriter::new().write(unbonding_period).build();

        Ok(PrecompileOutput {
            exit_status: ExitSucceed::Returned,
            cost: gasometer.used_gas(),
            output,
            logs: Default::default(),
        })
    }

    /// Fetch reward from EraRewardsAndStakes storage map
    fn read_era_reward(
        input: &mut EvmDataReader,
        gasometer: &mut Gasometer,
    ) -> EvmResult<PrecompileOutput> {
        input.expect_arguments(gasometer, 1)?;
        let era: u32 = input.read::<u32>(gasometer)?.into();
        let read_reward = pallet_dapps_staking::EraRewardsAndStakes::<R>::get(era);
        let reward = read_reward.map_or(Zero::zero(), |r| r.rewards);
        let reward = TryInto::<u128>::try_into(reward).unwrap_or(0);
        let output = EvmDataWriter::new().write(reward).build();

        Ok(PrecompileOutput {
            exit_status: ExitSucceed::Returned,
            cost: gasometer.used_gas(),
            output,
            logs: Default::default(),
        })
    }
    /// Fetch total staked amount from EraRewardsAndStakes storage map
    fn read_era_staked(
        input: &mut EvmDataReader,
        gasometer: &mut Gasometer,
    ) -> EvmResult<PrecompileOutput> {
        input.expect_arguments(gasometer, 1)?;
        let era: u32 = input.read::<u32>(gasometer)?.into();
        let reward_and_stake = pallet_dapps_staking::EraRewardsAndStakes::<R>::get(era);
        let staked = reward_and_stake.map_or(Zero::zero(), |r| r.staked);

        let staked = TryInto::<u128>::try_into(staked).unwrap_or(0);
        let output = EvmDataWriter::new().write(staked).build();

        Ok(PrecompileOutput {
            exit_status: ExitSucceed::Returned,
            cost: gasometer.used_gas(),
            output,
            logs: Default::default(),
        })
    }

    /// Fetch Ledger storage map
    fn read_staked_amount(
        input: &mut EvmDataReader,
        gasometer: &mut Gasometer,
    ) -> EvmResult<PrecompileOutput> {
        input.expect_arguments(gasometer, 1)?;

        let staker_h160 = input.read::<Address>(gasometer)?.0;
        let staker = R::AddressMapping::into_account_id(staker_h160);
        println!("read_staked_amount, staker={:?}", staker);

        // call pallet-dapps-staking
        let ledger = pallet_dapps_staking::Ledger::<R>::get(&staker);
        println!("read_staked_amount, ledger.locked={:?}", ledger.locked);

        // compose output
        let output = EvmDataWriter::new().write(ledger.locked).build();

        Ok(PrecompileOutput {
            exit_status: ExitSucceed::Returned,
            cost: gasometer.used_gas(),
            output,
            logs: Default::default(),
        })
    }

    /// Read the amount staked on contract in the given era
    fn read_contract_stake(
        input: &mut EvmDataReader,
        gasometer: &mut Gasometer,
    ) -> EvmResult<PrecompileOutput> {
        input.expect_arguments(gasometer, 1)?;

        // parse input parameters for pallet-dapps-staking call
        let contract_h160 = input.read::<Address>(gasometer)?.0;
        let contract_id = Self::decode_smart_contract(contract_h160)?;
        let current_era = pallet_dapps_staking::CurrentEra::<R>::get();

        // call pallet-dapps-staking
        let staking_info =
            pallet_dapps_staking::Pallet::<R>::staking_info(&contract_id, current_era);
        // encode output with total
        let total = TryInto::<u128>::try_into(staking_info.total).unwrap_or(0);
        let output = EvmDataWriter::new().write(total).build();

        Ok(PrecompileOutput {
            exit_status: ExitSucceed::Returned,
            cost: gasometer.used_gas(),
            output,
            logs: Default::default(),
        })
    }

    /// Register contract with the dapp-staking pallet
    fn register(
        input: &mut EvmDataReader,
        gasometer: &mut Gasometer,
        context: &Context,
    ) -> EvmResult<(
        <R::Call as Dispatchable>::Origin,
        pallet_dapps_staking::Call<R>,
    )> {
        input.expect_arguments(gasometer, 1)?;
        gasometer.record_cost(RuntimeHelper::<R>::db_read_gas_cost())?;

        // parse contract's address
        let contract_h160 = input.read::<Address>(gasometer)?.0;
        let contract_id = Self::decode_smart_contract(contract_h160)?;

        // Build call with origin.
        let origin = R::AddressMapping::into_account_id(context.caller);
        let call = pallet_dapps_staking::Call::<R>::register { contract_id }.into();

        // Return call information
        Ok((Some(origin).into(), call))
    }

    /// Lock up and stake balance of the origin account.
    fn bond_and_stake(
        input: &mut EvmDataReader,
        gasometer: &mut Gasometer,
        context: &Context,
    ) -> EvmResult<(
        <R::Call as Dispatchable>::Origin,
        pallet_dapps_staking::Call<R>,
    )> {
        println!("bond_and_stake, input={:?}", input);

        input.expect_arguments(gasometer, 1)?;
        println!("bond_and_stake, arguments OK");
        gasometer.record_cost(RuntimeHelper::<R>::db_read_gas_cost())?;
        println!("bond_and_stake, gasometer OK");

        // parse contract's address
        let contract_h160 = input.read::<Address>(gasometer)?.0;
        let contract_id = Self::decode_smart_contract(contract_h160)?;
        println!("bond_and_stake, contract_id OK");

        // parse balance to be staked
        let value: BalanceOf<R> = input.read(gasometer)?;
        println!("bond_and_stake, value={:?}", value);

        // Build call with origin.
        let origin = R::AddressMapping::into_account_id(context.caller);
        let call = pallet_dapps_staking::Call::<R>::bond_and_stake { contract_id, value }.into();

        // Return call information
        Ok((Some(origin).into(), call))
    }

    /// Start unbonding process and unstake balance from the contract.
    fn unbond_and_unstake(
        input: &mut EvmDataReader,
        gasometer: &mut Gasometer,
        context: &Context,
    ) -> EvmResult<(
        <R::Call as Dispatchable>::Origin,
        pallet_dapps_staking::Call<R>,
    )> {
        println!("unbond_and_unstake, input={:?}", input);

        input.expect_arguments(gasometer, 1)?;

        // parse contract's address
        let contract_h160 = input.read::<Address>(gasometer)?.0;
        let contract_id = Self::decode_smart_contract(contract_h160)?;

        // parse balance to be unstaked
        let value: BalanceOf<R> = input.read(gasometer)?;
        println!("unbond_and_unstake, value={:?}", value);
        // Build call with origin.
        let origin = R::AddressMapping::into_account_id(context.caller);
        let call =
            pallet_dapps_staking::Call::<R>::unbond_and_unstake { contract_id, value }.into();

        // Return call information
        Ok((Some(origin).into(), call))
    }

    /// Start unbonding process and unstake balance from the contract.
    fn withdraw_unbonded(
        context: &Context,
    ) -> EvmResult<(
        <R::Call as Dispatchable>::Origin,
        pallet_dapps_staking::Call<R>,
    )> {
        println!("withdraw_unbonded enter ");
        // Build call with origin.
        let origin = R::AddressMapping::into_account_id(context.caller);
        let call =
            pallet_dapps_staking::Call::<R>::withdraw_unbonded {}.into();

        // Return call information
        Ok((Some(origin).into(), call))
    }

    // /// Claim rewards for the contract in the dapp-staking pallet
    // fn claim(input: EvmInArg) -> Result<R::Call, PrecompileFailure> {
    //     input.expecting_arguments(2).map_err(|e| exit_error(e))?;

    //     // parse contract's address
    //     let contract_h160 = input.to_h160(1);
    //     let contract_id = Self::decode_smart_contract(contract_h160)?;

    //     // parse era
    //     let era = input.to_u256(2).low_u128().saturated_into();

    //     Ok(pallet_dapps_staking::Call::<R>::claim { contract_id, era }.into())
    // }

    /// Helper method to decode type SmartContract enum
    pub fn decode_smart_contract(
        contract_h160: H160,
    ) -> Result<<R as pallet_dapps_staking::Config>::SmartContract, PrecompileFailure> {
        // Encode contract address to fit SmartContract enum.
        // Since the SmartContract enum type can't be accessed from this pecompile,
        // use locally defined enum clone (see Contract enum)
        let contract_enum_encoded = Contract::<H160>::Evm(contract_h160).encode();

        // encoded enum will add one byte before the contract's address
        // therefore we need to decode len(H160) + 1 byte = 21
        let smart_contract = <R as pallet_dapps_staking::Config>::SmartContract::decode(
            &mut &contract_enum_encoded[..21],
        )
        .map_err(|_| exit_error("Error while decoding SmartContract"))?;

        Ok(smart_contract)
    }
}

#[precompile_utils::generate_function_selector]
#[derive(Debug, PartialEq)]
pub enum Action {
    ReadCurrentEra = "read_current_era()",
    ReadUnbondingPeriod = "read_unbonding_period()",
    ReadEraReward = "read_era_reward(uint32)",
    ReadEraStaked = "read_era_staked(uint32)",
    ReadStakedAmount = "read_staked_amount(address)",
    ReadContractStake = "read_contract_stake(address)",

    Register = "register(address)",
    BondAndStake = "bond_and_stake(address,uint128)",
    UnbondAndUnstake = "unbond_and_unstake(address,uint128)",
    WithdrawUnbounded = "withdraw_unbonded()",
}

impl<R> Precompile for DappsStakingWrapper<R>
where
    R: pallet_evm::Config + pallet_dapps_staking::Config,
    R::Call: From<pallet_dapps_staking::Call<R>>
        + Dispatchable<PostInfo = PostDispatchInfo>
        + GetDispatchInfo,
    <R::Call as Dispatchable>::Origin: From<Option<R::AccountId>>,
    BalanceOf<R>: EvmData,
{
    fn execute(
        input: &[u8],
        target_gas: Option<u64>,
        context: &Context,
        is_static: bool,
    ) -> EvmResult<PrecompileOutput> {
        // log::trace!(target: "ds-precompile", "In ds precompile");
        let mut gasometer = Gasometer::new(target_gas);
        let gasometer = &mut gasometer;

        let (mut input, selector) = EvmDataReader::new_with_selector(gasometer, input)?;
        let input = &mut input;

        gasometer.check_function_modifier(context, is_static, FunctionModifier::NonPayable)?;

        let (origin, call) = match selector {
            Action::ReadCurrentEra => return Self::read_current_era(gasometer),
            Action::ReadUnbondingPeriod => return Self::read_unbonding_period(gasometer),
            Action::ReadEraReward => return Self::read_era_reward(input, gasometer),
            Action::ReadEraStaked => return Self::read_era_staked(input, gasometer),
            Action::ReadStakedAmount => return Self::read_staked_amount(input, gasometer),
            Action::ReadContractStake => return Self::read_contract_stake(input, gasometer),
            // Dispatchables
            Action::Register => Self::register(input, gasometer, context)?,
            Action::BondAndStake => Self::bond_and_stake(input, gasometer, context)?,
            Action::UnbondAndUnstake => Self::unbond_and_unstake(input, gasometer, context)?,
            Action::WithdrawUnbounded => Self::withdraw_unbonded(context)?,

        };

        // Dispatch call (if enough gas).
        RuntimeHelper::<R>::try_dispatch(origin, call, gasometer)?;

        Ok(PrecompileOutput {
            exit_status: ExitSucceed::Returned,
            cost: gasometer.used_gas(),
            output: vec![],
            logs: vec![],
        })
        // let call = match selector {
        //     // storage getters
        //     [0xe6, 0x08, 0xd8, 0x0b] => return Self::read_current_era(),
        //     [0xdb, 0x62, 0xb2, 0x01] => return Self::read_unbonding_period(),
        //     [0xd9, 0x42, 0x4b, 0x16] => return Self::read_era_reward(input),
        //     [0x18, 0x38, 0x66, 0x93] => return Self::read_era_staked(input),
        //     [0x32, 0xbc, 0x5c, 0xa2] => return Self::read_staked_amount(input),
        //     [0x53, 0x9d, 0x59, 0x57] => return Self::read_contract_stake(input),

        //     // extrinsic calls
        //     [0x44, 0x20, 0xe4, 0x86] => Self::register(input)?,
        //     [0x52, 0xb7, 0x3e, 0x41] => Self::bond_and_stake(input)?,
        //     [0xc7, 0x84, 0x1d, 0xd2] => Self::unbond_and_unstake(input)?,
        //     [0x77, 0xa0, 0xfe, 0x02] => Self::withdraw_unbonded()?,
        //     [0xc1, 0x3f, 0x4a, 0xf7] => Self::claim(input)?,
        //     _ => {
        //         return Err(PrecompileFailure::Error {
        //             exit_status: ExitError::Other("No method at given selector".into()),
        //         });
        //     }
        // };

        // let info = call.get_dispatch_info();
        // if let Some(gas_limit) = target_gas {
        //     let required_gas = R::GasWeightMapping::weight_to_gas(info.weight);

        //     if required_gas > gas_limit {
        //         return Err(PrecompileFailure::Error {
        //             exit_status: ExitError::OutOfGas,
        //         });
        //     }
        // }

        // let origin = R::AddressMapping::into_account_id(context.caller);
        // let post_info = call.dispatch(Some(origin).into()).map_err(|e| {
        //     let error_text = match e.error {
        //         sp_runtime::DispatchError::Module { message, .. } => message,
        //         _ => Some("No error Info"),
        //     };
        //     exit_error(error_text.unwrap_or_default())
        // })?;

        // let gas_used =
        //     R::GasWeightMapping::weight_to_gas(post_info.actual_weight.unwrap_or(info.weight));

        // Ok(PrecompileOutput {
        //     exit_status: ExitSucceed::Returned,
        //     cost: gas_used,
        //     output: Default::default(),
        //     logs: Default::default(),
        // })
    }
}
